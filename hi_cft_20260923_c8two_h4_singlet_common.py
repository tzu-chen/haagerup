"""Immutable exact H4 block inputs and joint-singlet projection helpers."""
from collections import OrderedDict
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sqlite3
import zlib

import hi_cft_20260923_c8two_structure_saturation as auth
import hi_cft_20260923_next_n5_exact_selected as exact
import hi_cft_20260923_proof_general_modes_v2 as modes

x,b = auth.x,exact.b
MIB=1024**2
P=1000003


def factors():
    result=[]
    for axis,bound,e,f in (('LEFT',4,1,2),('RIGHT',24,4,5)):
        for h in range(2,bound+1,2):
            lam=h*(h+2)//4
            result.append({'axis':axis,'higher_weight':h,'e':e,'f':f,'lambda':lam})
    return result


def install(arithmetic):
    if arithmetic=='prime':
        assert auth.g3.install_prime(P)==[231543,1000]
    else:
        b.fast.install(x)
    exact.installed_modes()
    modes.MAX_GRADE=4


def digest(vector):
    record=[[list(s[0]),list(s[1]),int(c)] for s,c in sorted(vector.items()) if c]
    return hashlib.sha256(auth.compact(record).encode()).hexdigest()


class Inputs:
    def __init__(self,database,summary,arithmetic):
        self.path,self.summary=Path(database).resolve(),Path(summary).resolve()
        assert self.path.stat().st_size<=512*MIB and self.summary.stat().st_size<=8*MIB
        assert not Path(str(self.path)+'-journal').exists() and not Path(str(self.path)+'-wal').exists()
        self.db=sqlite3.connect(self.path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.db.execute('PRAGMA cache_size=-4096');self.db.execute('PRAGMA mmap_size=0')
        self.meta=json.loads(self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        saved=json.loads(self.summary.read_text())
        for key in ('format','weight','source_sha256','saved_terms','verified_targets','failed_targets','extended_columns'):
            assert saved[key]==self.meta[key]
        assert self.meta['format']=='exact-n4-selected-block-v1' and self.meta['weight']==[0,0]
        assert not self.meta['failed_targets'] and self.meta['extended_rank']<=300
        self.hashes={}
        auth.nested_graphs(self.meta,self.hashes)
        for path in (__file__,auth.__file__,exact.__file__,modes.__file__,self.path,self.summary):
            self.hashes[str(Path(path).resolve())]=auth.sha(path)
        self.columns=[i for i in self.meta['extended_columns'] if i>=0]
        assert len(self.columns)==279 and self.meta['extended_columns'][-1]==-2
        self.targets=[tuple(row) for row in self.meta['targeted_selection']['requested_targets']]
        assert len(self.targets)==12 and len(set(self.targets))==12
        assert all(0<=op<=8 and name.startswith('r3_') for op,name in self.targets)
        source=Path('hi_cft_20260923_c8_exact_fields.json').resolve()
        assert self.hashes[str(source)]==auth.sha(source)
        data=json.loads(source.read_text())['fields']
        assert len(data)==9
        self.ops=[x.read_field(row) for row in data]
        self.currents=x.LEFT+x.RIGHT
        self.arithmetic=arithmetic
        self.cache,self.cache_terms=OrderedDict(),0

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name)
            return self.cache[name]
        row=self.db.execute('SELECT record,digest,terms FROM vectors WHERE name=?',(name,)).fetchone()
        assert row is not None,('Missing frozen exact vector',name)
        blob,hashed,terms=row
        record=exact.unpack(blob,hashed)
        assert len(record)==terms<=12000
        vector={(tuple(a),tuple(o)):v for a,o,c in record if (v:=x.A(c))}
        assert len(vector)<=terms
        while self.cache and self.cache_terms+len(vector)>60000:
            _,previous=self.cache.popitem(last=False);self.cache_terms-=len(previous)
        self.cache[name]=vector;self.cache_terms+=len(vector)
        return vector

    def ordinary(self,word,mode):
        if word['kind']=='normal':
            assert word['column'] in self.columns
            return self.vector('normal:'+str(word['column']))
        assert word['kind']=='target' and (word['operator'],word['input']) in self.targets
        return mode(self.ops[word['operator']],0,self.vector('input:'+word['input']))


def project(vector,mode,currents,arithmetic,boundary=lambda:None):
    out=dict(vector);stopped=set()
    for factor in factors():
        if not out:break
        if factor['axis'] in stopped:continue
        raised=mode(currents[factor['e']],0,out)
        assert len(raised)<=12000;boundary()
        if arithmetic=='exact':
            assert max((b.height(c) for c in raised.values()),default=0)<=2048
        if not raised:
            stopped.add(factor['axis']);continue
        feedback=mode(currents[factor['f']],0,raised)
        assert len(feedback)<=12000;boundary()
        if arithmetic=='exact':
            assert max((b.height(c) for c in feedback.values()),default=0)<=2048
        coefficient=x.A(-1)/factor['lambda']
        for state,value in feedback.items():
            x.add(out,state,coefficient*value)
        del raised,feedback
        assert len(out)<=5000
        if arithmetic=='exact':
            assert max((b.height(c) for c in out.values()),default=0)<=2048
        boundary()
    assert all(x.grade(s)==4 and x.weight(s)==(0,0) for s in out)
    assert not mode(currents[1],0,out) and not mode(currents[4],0,out)
    return out
