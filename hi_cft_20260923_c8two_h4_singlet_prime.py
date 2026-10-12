"""Bounded projected normal-word pilot for the final twelve H4 singlets."""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_c8two_h4_singlet_common as c
import hi_cft_20260923_next_prime_mode_cache as helper
import hi_cft_20260923_next_n5_selected_pilot as serialization

FORMAT='H4-singlet-normal-prime-v1'


class Consumer:
    def __init__(self,args):
        self.args,self.started=args,monotonic();self.last=self.started
        self.output=Path(args.output);self.path=self.output.with_suffix('.sqlite')
        self.data=c.Inputs(args.database,args.source_summary,'prime')
        bindings=dict(self.data.hashes)
        for path in (__file__,helper.__file__,serialization.__file__):
            bindings[str(Path(path).resolve())]=c.auth.sha(path)
        assert all(p.resolve() not in {Path(f).resolve() for f in bindings}
                   for p in (self.output,self.path,self.output.with_suffix('.json.tmp')))
        self.cache=helper.PrimeModeCache(c.x,c.P,max_terms=300000,max_entries=50000)
        for field in [*self.data.currents,*self.data.ops]:self.cache.register(field)
        self.db=sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE');self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-4096');self.db.execute('PRAGMA mmap_size=0')
        self.db.execute('PRAGMA temp_store=FILE');self.db.execute('PRAGMA max_page_count=65536')
        assert self.db.execute('PRAGMA page_size').fetchone()[0]==4096
        self.db.execute('CREATE TABLE IF NOT EXISTS meta(id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS states(id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS rows(id INTEGER PRIMARY KEY,source_id INTEGER,pivot INTEGER,raw BLOB,reduced BLOB,word TEXT,digest TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS targets(id INTEGER PRIMARY KEY,raw BLOB,word TEXT,digest TEXT,residual BLOB)')
        self.db.commit();self.states=[];self.ids={};self.rows={};self.pivots={}
        previous=self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta=json.loads(previous[0]);assert self.meta['format']==FORMAT and self.meta['source_sha256']==bindings
            assert 0<=self.meta['cursor']<=len(self.data.columns)
            assert self.meta['target_count']==12 and self.meta['saved_terms']<=1200000
            for idx,value in self.db.execute('SELECT id,value FROM states ORDER BY id'):
                assert idx==len(self.states);a,o=json.loads(value);state=(tuple(a),tuple(o))
                assert c.x.grade(state)==4 and c.x.weight(state)==(0,0)
                self.states.append(state);self.ids[state]=idx
            assert len(self.states)==len(self.ids)==self.meta['state_count']<=5000
            for idx,source_id,pivot,reduced in self.db.execute('SELECT id,source_id,pivot,reduced FROM rows ORDER BY id'):
                assert idx==len(self.rows) and source_id<self.meta['cursor']
                row=dict(serialization.decode(reduced));self.rows[idx]=row;self.pivots[pivot]=idx
            assert len(self.rows)==len(self.pivots)==self.meta['rank']<=100
            target_ids=[row[0] for row in self.db.execute('SELECT id FROM targets ORDER BY id')]
            assert target_ids==list(range(len(target_ids))) and len(target_ids)<=12
            assert not self.meta['targets_ready'] or len(target_ids)==12
        else:
            self.meta={'format':FORMAT,'source_sha256':bindings,'prime':c.P,'roots':[231543,1000],
                'source_database':str(self.data.path),'source_summary':str(self.data.summary),
                'factors':c.factors(),'bounds':[4,24],'weight':[0,0],'cursor':0,'rank':0,
                'target_count':12,'targets_ready':False,'contained':0,'saved_terms':0,'history':[]}
        self.controls();self.save('Source and mode controls authenticated')

    def controls(self):
        word={'kind':'target','operator':self.data.targets[0][0],'input':self.data.targets[0][1]}
        expected=self.data.ordinary(word,self.cache.original_mode)
        actual=self.data.ordinary(word,self.cache.mode);assert actual==expected
        state=min(self.data.vector('normal:'+str(self.data.columns[0])))
        for current in self.data.currents:
            for scale in (1,7):
                assert self.cache.mode(current,0,{state:c.x.A(scale)})==self.cache.original_mode(current,0,{state:c.x.A(scale)})
        self.meta['controls']={'whole_target_original_mode_equal':True,'grade4_current_controls':12}

    def boundary(self):
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<1024*1024
        if monotonic()-self.started>=self.args.seconds:raise TimeoutError()

    def intern(self,vector):
        result={}
        for state,value in vector.items():
            if state not in self.ids:
                idx=len(self.states);assert idx<5000
                self.ids[state]=idx;self.states.append(state)
                self.db.execute('INSERT INTO states VALUES(?,?)',(idx,c.auth.compact(state)))
            result[self.ids[state]]=int(value)
        return result

    def reduce(self,vector):
        out=dict(vector)
        while out:
            pivot=min(out,key=lambda i:self.states[i])
            if pivot not in self.pivots:break
            coefficient=out[pivot]
            for state,value in self.rows[self.pivots[pivot]].items():
                new=(out.get(state,0)-coefficient*value)%c.P
                if new:out[state]=new
                else:out.pop(state,None)
        return out

    def check(self):
        count=0
        for idx,blob,digest in self.db.execute('SELECT id,raw,digest FROM targets ORDER BY id'):
            residual=self.reduce(dict(serialization.decode(blob,digest)))
            encoded,_=serialization.encode(sorted(residual.items()))
            self.db.execute('UPDATE targets SET residual=? WHERE id=?',(encoded,idx))
            count+=not residual
        self.meta['contained']=count
        return self.meta['targets_ready'] and count==12

    def save(self,reason,status='running'):
        self.meta.update(status=status,rank=len(self.rows),state_count=len(self.states),
            seconds=monotonic()-self.started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            scope='Prime projected-normal containment only; exact replay and raising premises required')
        self.meta['history'].append({'reason':reason,'rank':len(self.rows),'cursor':self.meta['cursor'],'contained':self.meta['contained']})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES(1,?)',(c.auth.compact(self.meta),));self.db.commit()
        c.auth.atomic(self.output,{**self.meta,'sqlite_file':str(self.path)})
        self.last=monotonic();c.b.clear_modes()
        print({key:self.meta[key] for key in ('status','rank','cursor','contained','seconds')},flush=True)

    def run(self):
        for idx,(op,name) in enumerate(self.data.targets):
            if self.db.execute('SELECT 1 FROM targets WHERE id=?',(idx,)).fetchone():continue
            recipe={'kind':'target','operator':op,'input':name}
            raw=self.data.ordinary(recipe,self.cache.mode)
            projected=c.project(raw,self.cache.mode,self.data.currents,'prime',self.boundary)
            vector=self.intern(projected);blob,digest=serialization.encode(sorted(vector.items()))
            word={'recipe':recipe,'factors':c.factors(),'ordinary_sha256':c.digest(raw)}
            self.db.execute('INSERT INTO targets VALUES(?,?,?,?,?)',(idx,blob,c.auth.compact(word),digest,None))
            self.meta['saved_terms']+=len(vector);self.save('One target projected')
        self.meta['targets_ready']=True
        if self.check():self.save('All saved targets contained','all_targets_contained');return
        while self.meta['cursor']<len(self.data.columns):
            index=self.meta['cursor'];column=self.data.columns[index]
            recipe={'kind':'normal','column':column};raw=self.data.ordinary(recipe,self.cache.mode)
            projected=c.project(raw,self.cache.mode,self.data.currents,'prime',self.boundary)
            vector=self.intern(projected);residual=self.reduce(vector)
            if residual:
                assert len(self.rows)<100,'100 projected rank review cap'
                pivot=min(residual,key=lambda i:self.states[i]);inv=pow(residual[pivot],-1,c.P)
                residual={i:value*inv%c.P for i,value in residual.items()}
                idx=len(self.rows);blob,digest=serialization.encode(sorted(vector.items()))
                reduced,_=serialization.encode(sorted(residual.items()))
                word={'recipe':recipe,'factors':c.factors(),'ordinary_sha256':c.digest(raw)}
                self.db.execute('INSERT INTO rows VALUES(?,?,?,?,?,?,?)',(idx,index,pivot,blob,reduced,c.auth.compact(word),digest))
                self.rows[idx]=residual;self.pivots[pivot]=idx
                self.meta['saved_terms']+=len(vector)+len(residual)
                assert self.meta['saved_terms']<=1200000
            self.meta['cursor']+=1
            if self.meta['cursor']%8==0 and self.check():
                self.save('All targets contained in projected normal subset','all_targets_contained');return
            if monotonic()-self.last>=20:self.save('Periodic projected-normal checkpoint')
            self.boundary()
        self.check();self.save('All selected normal columns processed',
            'all_targets_contained' if self.meta['contained']==12 else 'selected_family_exhausted')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_c8two_targeted_h4_support/block_p0_p0.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_c8two_targeted_h4_support/block_p0_p0.json')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_h4_singlet_prime.json')
    parser.add_argument('--seconds',type=int,default=300)
    args=parser.parse_args();assert 0<args.seconds<=600
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(args.seconds)
    c.install('prime');consumer=None
    try:consumer=Consumer(args);consumer.run()
    except (TimeoutError,MemoryError):
        if consumer:consumer.db.rollback()
        print({'status':'interrupted_prior_checkpoint_retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer:consumer.db.close();consumer.data.db.close()


if __name__=='__main__':main()
