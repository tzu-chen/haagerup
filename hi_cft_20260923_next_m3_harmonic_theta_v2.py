"""Small exact harmonic theta series for the level-21 Weil candidate.

Run only through hi_cft_safe_run.py. This constructs series, not a VOA
or a character identification. Rank-four lattice L7 + A2, det21;
two invariant harmonic quadratics yield weight-four cusp forms.
At most ten two-dimensional enumerations of a 41-square box, then
short sparse convolutions. Estimated peak <0.05 GiB; AS cap1GiB.
"""
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
from time import monotonic


def product(a, b, cutoff):
    out = defaultdict(F)
    for i, x in a.items():
        for j, y in b.items():
            if i+j <= cutoff:
                out[i+j] += x*y
    return {i:x for i,x in sorted(out.items()) if x}


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    started = monotonic()
    cutoff, bound = 210, 20
    seven, three = {}, {}
    # G7's smallest eigenvalue is3-sqrt2>1; A2's is1.
    # Hence norm<=20 forces each shifted coordinate squared<=20.
    # Every shift below has magnitude<2; the box bound20 is exhaustive.
    for r in range(7):
        theta, harmonic, energy = defaultdict(F), defaultdict(F), defaultdict(F)
        for i in range(-bound, bound+1):
            for j in range(-bound, bound+1):
                x, y = F(i)-F(r,7), F(j)+F(2*r,7)
                norm = 2*x*x+2*x*y+4*y*y
                k = 21*norm/2
                assert k.denominator == 1
                if k <= cutoff:
                    theta[int(k)] += 1
                    harmonic[int(k)] += 2*x*x+2*x*y-3*y*y
                    energy[int(k)] += norm
        seven[r] = (dict(theta),dict(harmonic),dict(energy))
    for s in range(3):
        theta, energy = defaultdict(F), defaultdict(F)
        for i in range(-bound, bound+1):
            for j in range(-bound, bound+1):
                x, y = F(i)+F(2*s,3), F(j)+F(s,3)
                norm = 2*x*x-2*x*y+2*y*y
                k = 21*norm/2
                assert k.denominator == 1
                if k <= cutoff:
                    theta[int(k)] += 1
                    energy[int(k)] += norm
        three[s] = (dict(theta),dict(energy))
    result = {}
    for r in range(7):
        for s in range(3):
            first = product(seven[r][1],three[s][0],cutoff)
            second = product(seven[r][2],three[s][0],cutoff)
            for k,v in product(seven[r][0],three[s][1],cutoff).items():
                second[k] = second.get(k,F(0))-v
            second = {k:v for k,v in sorted(second.items()) if v}
            assert not first.get(0) and not second.get(0)
            result[f'{r},{s}'] = [[str(k),str(v)] for k,v in first.items()], [[str(k),str(v)] for k,v in second.items()]
    assert result['1,0'] == result['6,0']
    assert result['0,1'] == result['0,2']
    # The zero-sector q coefficients are independent of any RCFT mapping.
    out = {'lattice_gram':[[2,1,0,0],[1,4,0,0],[0,0,2,-1],[0,0,-1,2]],
           'discriminant_quadratic_form':'r^2/7+s^2/3',
           'equivalent_generator':'Replacing r by3r gives2r^2/7+s^2/3.',
           'quadratics':['2x^2+2xy-3y^2','norm_L7-norm_A2'],
           'series_exponent_unit':'q^(1/21)', 'cutoff':cutoff,
           'coset_series':result, 'scope':'Harmonic theta forms only; modular representation and character matching need separate proof.',
           'seconds':monotonic()-started,
           'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=Path('hi_cft_20260923_next_m3_harmonic_theta_v2.json')
    assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k!='coset_series'},flush=True)
    print({key:result[key] for key in ('0,0','1,0','2,0','3,0')},flush=True)


if __name__ == '__main__':
    main()
