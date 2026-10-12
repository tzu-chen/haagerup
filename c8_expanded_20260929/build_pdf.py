#!/usr/bin/env python3
"""Bounded, non-numerical document typesetting only. No research commands.

The separate numerical lock is not used for this lightweight editorial
task. This runner accepts no arbitrary child commands, disables TeX shell
escape, and applies lower limits than the permanent numerical profile.
"""
from pathlib import Path
import argparse,json,os,resource,signal,subprocess,time

HERE=Path(__file__).resolve().parent
GIB=1024**3

def available():
    return int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024

def headroom():
    root=Path('/sys/fs/cgroup')
    relative=Path('/proc/self/cgroup').read_text().strip().split('::',1)[1]
    p=(root/relative.lstrip('/')).resolve()
    assert p.is_relative_to(root)
    room=float('inf')
    while True:
        if (p/'memory.max').exists() and (p/'memory.max').read_text().strip()!='max':
            room=min(room,int((p/'memory.max').read_text())-int((p/'memory.current').read_text()))
        if p==root:break
        p=p.parent
    return room

def rss(pgid):
    total=0
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:
            st=(p/'stat').read_text().rsplit(')',1)[1].split()
            if int(st[2])==pgid:total+=int(st[21])*os.sysconf('SC_PAGE_SIZE')
        except (OSError,ValueError,IndexError):pass
    return total

def run(passes):
    report={'scope':'Document typesetting only; no numerical research computation or certificate replay.',
            'limits':{'address_MiB':1536,'group_RSS_MiB':1024,'host_reserve_GiB':32,'CPUs':2,'threads':2,'seconds_per_pass':120},'passes':[]}
    for i in range(1,passes+1):
        if available()<32*GIB or headroom()<2*GIB:raise RuntimeError('Insufficient host/cgroup reserve for document build')
        aff=set(sorted(os.sched_getaffinity(0))[:2])
        def constrain():
            resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
            resource.setrlimit(resource.RLIMIT_CPU,(120,120))
            resource.setrlimit(resource.RLIMIT_CORE,(0,0))
            os.sched_setaffinity(0,aff)
        env=os.environ.copy()
        for key in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMBA_NUM_THREADS','JULIA_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS']:env[key]='2'
        logfile=HERE/f'build_pass_{i}.log'
        peak=0;begin=time.monotonic();minimum=available();reason=None
        with logfile.open('w') as out:
            child=subprocess.Popen(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error','haagerup_c8_expanded.tex'],cwd=HERE,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=constrain)
            try:
                while child.poll() is None:
                    peak=max(peak,rss(child.pid));minimum=min(minimum,available())
                    if peak>GIB:reason='document group RSS limit'
                    elif minimum<32*GIB:reason='host reserve'
                    elif headroom()<GIB:reason='cgroup reserve'
                    elif time.monotonic()-begin>120:reason='typesetting timeout'
                    if reason:os.killpg(child.pid,signal.SIGKILL);break
                    time.sleep(.2)
                code=child.wait()
            finally:
                if child.poll() is None:
                    os.killpg(child.pid,signal.SIGKILL);child.wait()
        record={'pass':i,'exit_code':code,'seconds':round(time.monotonic()-begin,3),'sampled_peak_RSS_MiB':round(peak/1024**2,3),'minimum_host_MemAvailable_GiB':round(minimum/GIB,3),'stop_reason':reason,'log':logfile.name}
        report['passes'].append(record)
        (HERE/'build_record.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if code or reason:
            print('\n'.join(logfile.read_text().splitlines()[-35:]),flush=True)
            raise SystemExit(code or 1)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--passes',type=int,default=3,choices=range(1,5));a=p.parse_args();run(a.passes)
