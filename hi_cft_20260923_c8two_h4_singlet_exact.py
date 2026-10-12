"""Exact projected identities for the twelve remaining H4 outputs.

This certifies only joint-singlet projected containment. Separate exact
raising premises are required before recovering unprojected H4 membership.
"""
import argparse
from collections import OrderedDict
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_c8two_h4_singlet_common as c
import hi_cft_20260923_next_n5_projected_exact as base
import hi_cft_20260923_next_exact_mode_cache as helper

b,raw=c.b,c.exact
FORMAT='exact-H4-singlet-normal-relations-v1'


class Consumer(raw.ExactSelected):
    def __init__(self,args):
        self.args,self.started=args,monotonic();self.last_save=self.started
        self.output,self.path=Path(args.output),Path(args.output).with_suffix('.sqlite')
        source,summary=Path(args.database).resolve(),Path(args.source_summary).resolve()
        assert source.stat().st_size<=256*c.MIB and summary.stat().st_size<=8*c.MIB
        assert not Path(str(source)+'-journal').exists() and not Path(str(source)+'-wal').exists()
        self.source=sqlite3.connect(source.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096');self.source.execute('PRAGMA mmap_size=0')
        self.pm=json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['format']=='H4-singlet-normal-prime-v1' and self.pm['prime']==c.P
        assert self.pm['factors']==c.factors() and self.pm['targets_ready'] and self.pm['target_count']==12
        saved=json.loads(summary.read_text())
        for key in ('format','source_sha256','cursor','rank','targets_ready','target_count','state_count'):
            assert saved[key]==self.pm[key]
        bindings={};c.auth.verify_graph(self.pm['source_sha256'],bindings)
        self.data=c.Inputs(self.pm['source_database'],self.pm['source_summary'],'exact')
        c.auth.verify_graph(self.data.hashes,bindings)
        for path in (__file__,base.__file__,helper.__file__,source,summary):
            bindings[str(Path(path).resolve())]=c.auth.sha(path)
        for path in (self.output,self.path,self.output.with_suffix('.json.tmp')):
            assert path.resolve() not in {Path(filename).resolve() for filename in bindings}
        self.states={}
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx==len(self.states) and idx<5000
            a,o=json.loads(value);state=(tuple(a),tuple(o))
            assert c.x.grade(state)==4 and c.x.weight(state)==(0,0)
            self.states[idx]=state
        assert len(self.states)==len(set(self.states.values()))==self.pm['state_count']
        self.blocks={(0,0):[]}
        for idx,source_id,pivot in self.source.execute('SELECT id,source_id,pivot FROM rows ORDER BY id'):
            assert idx==len(self.blocks[(0,0)]) and 0<=source_id<self.pm['cursor']
            self.blocks[(0,0)].append((idx,self.states[pivot]))
        assert len(self.blocks[(0,0)])==self.pm['rank']<=100
        self.targets=[]
        for idx,word in self.source.execute('SELECT id,word FROM targets ORDER BY id'):
            assert idx==len(self.targets)
            word=json.loads(word);recipe=word['recipe']
            assert word['factors']==c.factors() and recipe['kind']=='target'
            assert (recipe['operator'],recipe['input'])==self.data.targets[idx]
            self.targets.append((idx,(0,0),word))
        assert len(self.targets)==12
        native_control=Path('hi_cft_20260923_next_flint_field_check.json').resolve()
        control=json.loads(native_control.read_text())
        assert control['status']=='exact_flint_regular_representation_controls_passed'
        c.auth.verify_graph(control['source_sha256'],bindings)
        bindings[str(native_control)]=c.auth.sha(native_control)
        bindings[str(Path(raw.h4.native.__file__).resolve())]=c.auth.sha(raw.h4.native.__file__)
        self.flint=raw.h4.native.Flint()
        self.mode_cache=helper.ExactModeCache(c.x,b.fast.FastField,max_bytes=128*c.MIB,max_entries=20000)
        for field in [*self.data.currents,*self.data.ops]:self.mode_cache.register(field)
        self.db=sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE');self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-4096');self.db.execute('PRAGMA mmap_size=0')
        self.db.execute('PRAGMA temp_store=FILE');self.db.execute('PRAGMA max_page_count=65536')
        assert self.db.execute('PRAGMA page_size').fetchone()[0]==4096
        self.db.execute('CREATE TABLE IF NOT EXISTS meta(id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS vectors(name TEXT PRIMARY KEY,record BLOB,digest TEXT,terms INTEGER,bits INTEGER)')
        self.db.execute('CREATE TABLE IF NOT EXISTS relations(id INTEGER PRIMARY KEY,record BLOB,digest TEXT,passed INTEGER)')
        self.db.commit();self.cache,self.cache_bytes=OrderedDict(),0
        previous=self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta=json.loads(previous[0])
            assert self.meta['format']==FORMAT and self.meta['source_sha256']==bindings
            assert self.db.execute('SELECT COUNT(*) FROM relations').fetchone()[0]==self.meta['verified_targets']+self.meta['failed_targets']
        else:
            self.meta={'format':FORMAT,'source_sha256':bindings,'saved_terms':0,'verified_targets':0,
                'failed_targets':0,'target_count':12,'status':'running','history':[],
                'largest_vector_bits':0,'largest_relation_bits':0,'completed_blocks':[],
                'factors':c.factors(),'unprojected_H4_membership_claimed':False}
        state=min(self.data.vector('normal:'+str(self.data.columns[0])))
        for current in self.data.currents:
            for scalar in (b.fast.ONE,b.fast.FastField((1,1,0,0))):
                right={state:scalar}
                assert self.mode_cache.mode(current,0,right)==self.mode_cache.original_mode(current,0,right)
        self.meta['grade4_current_original_mode_controls']=12
        self.save('Exact joint-singlet consumer authenticated')

    def cache_put(self,name,vector,bits):
        return base.Consumer.cache_put(self,name,vector,bits)

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name);return self.cache[name][0]
        previous=self.db.execute('SELECT record,digest,terms,bits FROM vectors WHERE name=?',(name,)).fetchone()
        if previous:
            blob,digest,terms,bits=previous;record=raw.unpack(blob,digest)
            assert len(record)==terms<=5000 and bits<=2048
            vector={(tuple(a),tuple(o)):b.fast.FastField(q) for a,o,q in record}
            assert len(vector)==terms;self.cache_put(name,vector,bits);return vector
        kind,idx=name.split(':');idx=int(idx);assert kind in ('grade5','target')
        table='rows' if kind=='grade5' else 'targets'
        blob,word,digest=self.source.execute(f'SELECT raw,word,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        word=json.loads(word);assert word['factors']==c.factors()
        assert word['recipe']['kind']==('normal' if kind=='grade5' else 'target')
        ordinary=self.data.ordinary(word['recipe'],self.mode_cache.mode)
        assert len(ordinary)<=5000 and all(c.x.grade(s)==4 and c.x.weight(s)==(0,0) for s in ordinary)
        residues={s:r for s,v in ordinary.items() if (r:=b.specialization(v))}
        assert c.digest(residues)==word['ordinary_sha256']
        vector=c.project(ordinary,self.mode_cache.mode,self.data.currents,'exact',self.boundary)
        expected={self.states[i]:value for i,value in raw.unpack(blob,digest)}
        residues={s:r for s,v in vector.items() if (r:=b.specialization(v))}
        assert residues==expected,'Full projected specialization mismatch'
        return self.store(name,vector)

    def save(self,reason,status='running'):
        self.meta.update(status=status,seconds_this_call=monotonic()-self.started,
            peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            scope='Exact joint-singlet projected identities only. Unprojected H4 membership requires the separate raising-premise certificate.',
            source_target_words=[word for _,_,word in self.targets],
            native_solver={'version':self.flint.version,'threads':1})
        self.meta['history'].append({'reason':reason,'verified_targets':self.meta['verified_targets'],
                                    'failed_targets':self.meta['failed_targets'],'seconds':self.meta['seconds_this_call']})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES(1,?)',(c.auth.compact(self.meta),));self.db.commit()
        c.auth.atomic(self.output,{**self.meta,'sqlite_file':str(self.path)})
        self.last_save=monotonic();b.clear_modes()
        print({key:self.meta[key] for key in ('status','verified_targets','failed_targets','seconds_this_call')},flush=True)

    def close(self,rollback=False):
        if rollback:self.db.rollback()
        self.db.close();self.source.close();self.data.db.close()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_c8two_h4_singlet_prime.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_c8two_h4_singlet_prime.json')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_h4_singlet_exact.json')
    parser.add_argument('--seconds',type=int,default=600)
    args=parser.parse_args();args.weight=None;args.max_rank=100
    assert 0<args.seconds<=900 and 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(args.seconds)
    c.install('exact');consumer=None;rollback=False
    try:consumer=Consumer(args);consumer.run()
    except b.BudgetStop as error:
        signal.alarm(0)
        if consumer is None:raise
        consumer.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        rollback=True
        print({'status':'interrupted_prior_exact_checkpoints_retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer:consumer.close(rollback)


if __name__=='__main__':main()
