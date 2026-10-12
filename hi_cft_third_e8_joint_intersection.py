"""Intersect frozen E8 witnesses with exact orthogonal ground constraints.

Pure standard library, coordinated128MiB launcher only. This reads saved
necessary witnesses; it does not construct a VOA or identify the H3 chain.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import resource


DESCRIPTION = re.compile(r'A1_(\d+)(?: x A1_(\d+))? \+ U1\^(\d+)')


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def read(path):
    if path.stat().st_size > 2*1024**2:
        raise ValueError('JSON exceeds reviewed2MiB size')
    raw = path.read_bytes()
    if len(raw) > 2*1024**2:
        raise ValueError('JSON grew past reviewed size')
    return json.loads(raw),hashlib.sha256(raw).hexdigest()


def intersect(grid,joint,rank3):
    if not joint['bilinear_parity_filter_applied'] or not joint['d6_dimension_filter_applied'] or not joint['d5_dimension_filter_applied']:
        raise ValueError('Complete orthogonal d5/d6 filter required')
    if rank3['rank_three_necessary_levels_without_module_energy_bounds'] != [1,2]:
        raise ValueError('Unexpected rank3 certificate')
    energy = joint['affine_energy_filter_applied']
    allowed = {tuple(row['levels']) for row in joint['d6_dimension_levels']}
    if len(allowed) != joint['d6_dimension_summary']['level_pair_count']:
        raise ValueError('Repeated or inconsistent level list')
    pair_floor = min((F(2)+F(6,k+2)+F(6,l+2) for k,l in allowed),default=None)
    if pair_floor != F(joint['d6_dimension_summary']['residual_lower_bound']):
        raise ValueError('Incorrect saved pair minimum')
    # At k2 the required d1 triplet has affine weight1/2 >6/13.
    # Applying this exclusion explicitly uses the selected module-energy premise.
    rank3_levels = {1} if energy else {1,2}
    floor = min(pair_floor,min(F(5)-F(3*k,k+2) for k in rank3_levels))
    kept,rejected = [],[]
    hosts = grid['remaining_full_current_hosts']
    if len(hosts) != grid['remaining_full_current_hosts_count'] or len(hosts)>157:
        raise ValueError('Unexpected full-current host domain')
    for row in hosts:
        match = DESCRIPTION.fullmatch(row['factor_description'])
        if not match or row['W1_dimension'] != 6:
            raise ValueError('Expected previously filtered gamma0 current host')
        levels = sorted(int(v) for v in match.group(1,2) if v is not None)
        radical = int(match.group(3))
        if radical != row['abelian_rank'] or 3*len(levels)+radical != 6:
            raise ValueError('Current description disagrees with host dimensions')
        residual = F(8)-radical-sum((F(3*k,k+2) for k in levels),F(0))
        if residual != F(row['residual_c']):
            raise ValueError('Saved residual disagrees with exact Sugawara subtraction')
        passes = (radical==3 and len(levels)==1 and levels[0] in rank3_levels) or (radical==0 and tuple(levels) in allowed)
        (kept if passes else rejected).append(row)
    if any(F(row['residual_c']) < floor for row in kept):
        raise AssertionError('Intersection violates its universal bound')
    return {'additional_nonvacuum_module_energy_premise':energy,
        'abstract_current_coset_lower_bound':str(floor),
        'input_full_host_count':len(hosts),'remaining_full_host_count':len(kept),
        'catalog_minimum_full_current_residual_c':str(min(F(r['residual_c']) for r in kept)) if kept else None,
        'rank3_necessary_levels':sorted(rank3_levels),'allowed_pair_levels':sorted(allowed),
        'remaining_full_current_hosts':kept,'newly_rejected_full_current_hosts':rejected,
        'scope':'Necessary full-current hosts within the earlier E8 catalog. The abstract bound applies under the parent VOA assumptions to all current-generated denominators; this catalog minimum uses the saved E8 embedding enumeration. No non-current denominator or physical-chain exclusion follows. Empty previously bounded denominator rows are not a full CFT classification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid',type=Path,default=Path('hi_cft_third_e8_flavoured_grid_results.json'))
    parser.add_argument('--rank3',type=Path,default=Path('hi_cft_third_gamma0_rank3_results.json'))
    parser.add_argument('--joint',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap >128*1024**2:
        raise RuntimeError('Use the coordinated128MiB launcher')
    paths = [p.resolve() for p in (args.grid,args.joint,args.rank3)]
    output = args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output in paths:
        raise ValueError('Choose a new noncolliding.json output')
    loaded = [read(p) for p in paths]
    hashes = {str(p):item[1] for p,item in zip(paths,loaded)}
    source = Path(__file__).resolve()
    hashes[str(source)] = digest(source)
    result = intersect(*(item[0] for item in loaded))
    result['input_and_reader_sha256'] = hashes
    if any(digest(p)!=h for p,h in hashes.items()):
        raise RuntimeError('Input or reader changed')
    try:
        with pending.open('x') as stream:
            json.dump(result,stream,indent=2,allow_nan=False)
            stream.write('\n')
        if output.exists() or any(digest(p)!=h for p,h in hashes.items()):
            raise RuntimeError('Input, reader or output changed before promotion')
        pending.replace(output)
    finally:
        if pending.exists():pending.unlink()
    print(json.dumps({k:result[k] for k in ('remaining_full_host_count','abstract_current_coset_lower_bound','catalog_minimum_full_current_residual_c')}))


if __name__ == '__main__':main()
