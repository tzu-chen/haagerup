"""Finish closed H4 certificates with exact column rescaling, unchanged caps.

This creates a new closed-copy lineage. Native solutions in scaled columns
are converted to original normal-word coefficients before the frozen full
integer residual. Scaling is accepted only when it lowers column height.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import resource
import signal
import sys

import hi_cft_20260923_c8two_structure_h4_trim_v2 as old

b,bulk = old.b,old.bulk
MIB = 1024**2
STATE = {}


def prepare(origin,destination,request):
    origin,destination,request = map(lambda p:Path(p).resolve(),(origin,destination,request))
    assert origin.is_dir() and origin != destination
    assert origin not in destination.parents and destination not in origin.parents
    assert not any(origin.glob('*-journal')) and not any(origin.glob('*-wal'))
    files = sorted(p for p in origin.iterdir() if p.suffix in ('.json','.sqlite'))
    assert 0 < len(files) <= 200
    assert all(p.is_file() and not p.is_symlink() and p.stat().st_size <= 512*MIB for p in files)
    assert sum(p.stat().st_size for p in files) <= 4*1024**3
    legacy = json.loads((origin/'targeted_policy.json').read_text())
    trim = json.loads((origin/'pre_native_trim_lineage.json').read_text())
    summary = json.loads((origin/'summary.json').read_text())
    assert legacy['format'] == 'targeted-H4-integer-residual-v1' and summary['policy'] == legacy
    assert trim['format'] == 'targeted-H4-pre-native-cache-trim-v2'
    assert trim['legacy_targeted_policy'] == legacy
    assert summary['status'] in ('bounded_stop','interrupted_exact_checkpoints_retained',
                                 'all_requested_exact_H4_targets_passed')
    old.auth.nested_graphs(legacy,{})
    old.auth.nested_graphs(trim,{})
    assert legacy['source_sha256'][str(request)] == b.sha(request)
    lineage = {'format':'targeted-H4-exact-column-normalization-v1',
        'source_sha256':{str(Path(path).resolve()):b.sha(path)
                         for path in (__file__,old.__file__,old.old.__file__,request)},
        'ancestor_directory':str(origin),'ancestor_files_sha256':{str(p):b.sha(p) for p in files},
        'legacy_trim_policy':trim,'legacy_targeted_policy':legacy,
        'native_preflight_limit_bytes':512*MIB,'rank_limit':300,
        'normalization_rule':'Choose a rational primitive-content or field-entry scale only if exact column height decreases; undo in original-word coefficients before full residual'}
    manifest = destination/'column_normalization_lineage.json'
    if destination.exists():
        assert manifest.exists() and json.loads(manifest.read_text()) == lineage
    else:
        temporary = destination.with_name(destination.name+'.importing')
        assert not temporary.exists()
        temporary.mkdir()
        for source in files:
            digest = hashlib.sha256()
            with source.open('rb') as src,(temporary/source.name).open('xb') as dst:
                while chunk := src.read(MIB):
                    digest.update(chunk);dst.write(chunk)
            assert digest.hexdigest() == lineage['ancestor_files_sha256'][str(source)]
            assert b.sha(temporary/source.name) == digest.hexdigest()
        bulk.atomic_json(temporary/'column_normalization_lineage.json',lineage)
        temporary.replace(destination)
    return lineage,trim,legacy


def rational_scale(column):
    denominator = 1
    for value in column:
        for q in value:
            den = int(q.denominator)
            denominator = denominator//gcd(denominator,den)*den
            if denominator.bit_length() > 4096:
                return None
    content = 0
    for value in column:
        for q in value:
            content = gcd(content,abs(int(q.numerator)*(denominator//int(q.denominator))))
    assert content
    return b.fast.FastField(denominator)/content


class Consumer(old.Consumer):
    def __init__(self,args,serial_policy,targeted_policy,selection):
        super().__init__(args,serial_policy,targeted_policy,selection)
        self.normalization_scales = None
        previous = self.meta.get('column_normalization')
        if previous is None:
            self.meta['column_normalization'] = {'policy':STATE['lineage'],'events':[]}
        else:
            assert previous['policy'] == STATE['lineage']
        self.save('Exact column normalization lineage authenticated')

    def matrix(self):
        matrix = super().matrix()
        scales,events = [],[]
        for j,index in enumerate(self.columns):
            column = [row[j] for row in matrix]
            before = max(b.height(value) for value in column)
            best,scale,after = column,b.fast.ONE,before
            candidates = []
            primitive = rational_scale(column)
            if primitive is not None:
                candidates.append(primitive)
            nonzero = [value for value in column if value]
            assert nonzero
            # The inverse of a small nonzero entry removes any common field
            # factor; it is merely a scalar basis change, not row elimination.
            candidates.append(min(nonzero,key=b.height).inv())
            for candidate in candidates:
                if b.height(candidate) > 4096:
                    continue
                trial = [candidate*value for value in column]
                bits = max(b.height(value) for value in trial)
                if bits < after:
                    best,scale,after = trial,candidate,bits
            assert scale and all(scale*value == changed for value,changed in zip(column,best))
            for i,value in enumerate(best):
                matrix[i][j] = value
            scales.append(scale)
            if after < before:
                events.append({'column':index,'before_bits':before,'after_bits':after,
                               'scale':[str(q) for q in scale]})
            self.boundary()
        self.normalization_scales = scales
        self.meta['column_normalization']['events'].append({
            'rank':self.r,'changed_columns':events,
            'normalized_matrix_bits':max(b.height(value) for row in matrix for value in row)})
        self.save('Exact column scalings checked; native preflight remains unchanged')
        return matrix

    def verify_ready(self,op,name,target,coefficients):
        assert self.normalization_scales is not None and len(coefficients) == len(self.normalization_scales)
        original = [scale*c for scale,c in zip(self.normalization_scales,coefficients)]
        assert max((b.height(c) for c in original),default=0) <= b.MATRIX_BITS
        return super().verify_ready(op,name,target,original)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-directory',default='hi_cft_20260923_c8two_targeted_h4_trimmed_v2')
    parser.add_argument('--output-directory',default='hi_cft_20260923_c8two_targeted_h4_normalized')
    parser.add_argument('--request',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--seconds',type=int,default=600)
    args,remaining = parser.parse_known_args()
    assert 0 < args.seconds <= 900 and 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    STATE['lineage'],old.STATE['lineage'],old.STATE['legacy'] = prepare(
        args.import_directory,args.output_directory,args.request)
    old.old.Consumer = Consumer
    sys.argv = [old.old.__file__,'--request',args.request,'--output-directory',args.output_directory,
                '--seconds',str(args.seconds),'--batch',str(old.STATE['legacy']['batch']),*remaining]
    old.old.main()


if __name__ == '__main__':
    main()
