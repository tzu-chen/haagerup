"""Fresh targeted H4 identities with the frozen pre-native cache trim.

Uses the unchanged targeted loop, exact native solver and full integer
residual. No source directory is copied and no old policy is rewritten.
Root-only numerical job; this source itself authorizes no launch.
"""
import argparse
import json
from pathlib import Path
import resource
import sys

import hi_cft_20260923_c8two_structure_h4_trim_v2 as trim

old,b,auth=trim.old,trim.b,trim.auth
STATE={}


class Consumer(old.Consumer):
    def __init__(self,args,serial_policy,targeted_policy,selection):
        super().__init__(args,serial_policy,targeted_policy,selection)
        previous=self.meta.get('pre_native_trim_v2')
        if previous is None:
            self.meta['pre_native_trim_v2']={'policy':STATE['policy'],'events':[]}
        else:
            assert previous['policy']==STATE['policy']
        self.flint=trim.TrimmedSolve(self.flint,self)
        self.save('Fresh targeted certificate bound to unchanged pre-native cache trim')

    trim_before_native=trim.Consumer.trim_before_native


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request',default='hi_cft_20260923_c8two_structure_h4_raise_request.json')
    parser.add_argument('--output-directory',default='hi_cft_20260923_c8two_structure_h4_raised_exact')
    parser.add_argument('--seconds',type=int,default=300)
    args,remaining=parser.parse_known_args()
    assert 0<args.seconds<=900 and 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    request,output=Path(args.request).resolve(),Path(args.output_directory).resolve()
    assert request.stat().st_size<=4*1024**2
    data=json.loads(request.read_text())
    assert data['format']=='H4-raising-residual-support-request-v1'
    assert len(data['additional_tests'])==12
    assert all(row['output_weight']==[0,2] for row in data['additional_tests'])
    sources={}
    auth.verify_graph(data['source_sha256'],sources)
    for p in (__file__,trim.__file__,old.__file__,request):
        sources[str(Path(p).resolve())]=auth.sha(p)
    assert str(output) not in sources and output!=request.parent
    STATE['policy']={'format':'fresh-targeted-H4-pre-native-trim-v1',
        'source_sha256':sources,'scope':'Unchanged exact full residual; only reconstructible caches are released before the native solve.'}
    manifest=output/'fresh_trim_policy.json'
    if output.exists():
        assert manifest.exists() and json.loads(manifest.read_text())==STATE['policy']
    else:
        output.mkdir()
        old.bulk.atomic_json(manifest,STATE['policy'])
    old.Consumer=Consumer
    sys.argv=[old.__file__,'--request',str(request),'--output-directory',str(output),
              '--seconds',str(args.seconds),'--batch','3',*remaining]
    old.main()


if __name__=='__main__':main()
