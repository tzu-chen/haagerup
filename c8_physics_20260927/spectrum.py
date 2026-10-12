#!/usr/bin/env python3
"""Exact c=8 character, Virasoro-primary, and diagonal-spectrum data.

ROOT alone runs this source, through hi_cft_safe_run.py.  Standard library
only; no research-engine imports, subprocesses, workers, or dense spaces.
Default: 24 chiral grades and complete full-CFT spectrum through Delta=24.
Reviewed bound: order <=64, <128 MiB expected RSS; request 512 MiB AS.

The input is Evans--Gannon arXiv:1006.1326, Sections 1.4 and 2.4.
The recurrence is derived from the differential equation below, so its
convolution index is unambiguous even in renderings of (1.24) with g[n-1].
Numerical thermal intervals use directed Decimal arithmetic at 80 digits.
"""

import argparse
from collections import defaultdict
from decimal import Decimal as D, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
from time import monotonic

NAMES = ('0', 'b', 'a', 'c0', 'c1', 'c2', 'd1', 'd2', 'd3', 'd4', 'd5', 'd6')
LAM = tuple(F(x) for x in ('2/3','2/3','2/3','2/3','0','1/3',
                          '5/39','20/39','32/39','2/39','8/39','11/39'))
CHI = (
    (6,80,81,81,8748,1215,3549,273,13,5538,2275,1378),
    (80,6,81,81,8748,1215,-3549,-273,-13,-5538,-2275,-1378),
    (81,81,167,-81,-8748,-1215,0,0,0,0,0,0),
    (81,81,-81,167,-8748,-1215,0,0,0,0,0,0),
    (3,3,-3,-3,-12,18,0,0,0,0,0,0),
    (27,27,-27,-27,1458,-152,0,0,0,0,0,0),
    (7,-7,0,0,0,0,-88,-14,-1,50,63,64),
    (42,-42,0,0,0,0,-1484,92,16,2940,-192,-1041),
    (119,-119,0,0,0,0,-2142,987,11,-24990,-6035,4641),
    (5,-5,0,0,0,0,17,13,-3,-2,35,-14),
    (13,-13,0,0,0,0,174,-1,-5,294,-147,51),
    (14,-14,0,0,0,0,448,-77,7,-343,125,-24))
PUBLISHED = (
    (6,80,81,81,3,27,7,42,119,5,13,14),
    (120,1250,1377,1377,243,594,292,777,1623,229,347,441),
    (956,10630,11583,11583,2916,5967,3204,7147,12996,2738,3804,4445),
    (6010,65042,71037,71037,21870,39852,23010,45367,76429,19942,26390,30329))
SOURCE_URL = 'https://arxiv.org/abs/1006.1326'
ROOT = Path(__file__).resolve().parent.parent
PREC = 80
# 100 digits after the decimal point, truncated downward; upper = lower+10^-100.
PI_LO = '3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, D):
        return str(value)
    if isinstance(value, Interval):
        return {'lower': str(value.lo), 'upper': str(value.hi)}
    raise TypeError(type(value).__name__)


def mul(a, b, n):
    return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(n+1)]


def div_unit(a, b, n):
    assert b[0] == 1
    out = []
    for i in range(n+1):
        out.append(a[i]-sum(b[j]*out[i-j] for j in range(1, i+1)))
    return out


def scalar_series(n):
    sig3 = [0]*(n+1)
    sig5 = [0]*(n+1)
    for d in range(1, n+1):
        for j in range(d, n+1, d):
            sig3[j] += d**3
            sig5[j] += d**5
    e4 = [1]+[240*x for x in sig3[1:]]
    e6 = [1]+[-504*x for x in sig5[1:]]
    e4sq = mul(e4, e4, n)
    delta_numerators = [a-b for a,b in zip(mul(e4sq,e4,n), mul(e6,e6,n))]
    assert all(x % 1728 == 0 for x in delta_numerators)
    delta = [x//1728 for x in delta_numerators]
    g = div_unit(delta, mul(e4,e6,n), n)
    f = [a-984*b for a,b in zip(div_unit(e4sq,e6,n), g)]
    assert f[:2] == [1,0] and g[:3] == [0,1,240]
    return f, g, e4


def matmul(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(12)), F(0))
             for j in range(12)] for i in range(12)]


def xi_coefficients(order):
    """X[n] in Xi=q^Lambda sum[n>=-1] X[n]q^n, through n=order.

    D Xi = Xi[(J-240)g(Lambda-I)+g C], C=chi+[Lambda,chi].
    Cache X[n]C once.  Time O(order*12^3+order^2*12^2), not O(order^2*12^3).
    """
    f, g, e4 = scalar_series(order+1)
    c = [[(1+LAM[i]-LAM[j])*CHI[i][j] for j in range(12)] for i in range(12)]
    x = {-1:[[F(i == j) for j in range(12)] for i in range(12)]}
    xc = {-1:c}
    for n in range(order+1):
        rhs = [[F(0) for j in range(12)] for i in range(12)]
        for r in range(1,n+2):
            p, pc = x[n-r], xc[n-r]
            for i in range(12):
                for j in range(12):
                    rhs[i][j] += f[r]*(LAM[j]-1)*p[i][j]+g[r]*pc[i][j]
        x[n] = [[rhs[i][j]/(n+1+LAM[i]-LAM[j]) for j in range(12)] for i in range(12)]
        xc[n] = matmul(x[n], c)
    assert x[0] == [list(map(F,row)) for row in CHI]
    for n, expected in enumerate(PUBLISHED):
        assert [x[n][i][0] for i in range(12)] == list(expected), (n, 'published coefficient')
    return x, f, g, e4


def euler_product(order):
    p = [1]+[0]*order
    for n in range(1,order+1):
        for k in range(order,n-1,-1):
            p[k] -= p[k-n]
    return p


def partitions(order):
    p = [1]+[0]*order
    for n in range(1,order+1):
        for k in range(n,order+1):
            p[k] += p[k-n]
    return p


def primaries(dimensions, vacuum, euler, part):
    n = len(dimensions)-1
    p = mul(dimensions, euler, n)
    if vacuum:
        # Include the identity once, but replace the vacuum Verma character
        # by (1-q)/Euler.  Thus P_total=Euler*V+q.
        p[1] += 1
    assert all(x >= 0 and isinstance(x,int) for x in p)
    rebuilt = mul(p, part, n)
    if vacuum:
        rebuilt = [v-(part[k-1] if k else 0) for k,v in enumerate(rebuilt)]
    assert rebuilt == dimensions, 'independent descendant reconstruction'
    return p


def chiral_data(order, x, e4):
    euler, part = euler_product(order), partitions(order)
    assert mul(euler,part,order) == [1]+[0]*order
    modules = []
    for i,name in enumerate(NAMES):
        start = -1 if i == 0 else 0
        raw = [x[start+n][i][0] for n in range(order+1)]
        assert all(a.denominator == 1 and a >= 0 for a in raw)
        dims = [int(a) for a in raw]
        modules.append({'module': name, 'h': LAM[i]+start+F(1,3),
                        'state_multiplicities': dims,
                        'virasoro_primary_multiplicities_including_identity':
                            primaries(dims,i == 0,euler,part)})
    assert modules[0]['h'] == 0 and modules[8]['h'] == F(15,13)
    assert modules[0]['virasoro_primary_multiplicities_including_identity'][:5] == [1,6,113,830,4934]
    # Independent holomorphic E8 character, E4/eta^8.
    oscillator8 = [1]+[0]*order
    for unused in range(8):
        oscillator8 = mul(oscillator8,part,order)
    e8dims = mul(e4[:order+1],oscillator8,order)
    assert e8dims[:4] == [1,248,4124,34752]
    # A scalar character identity only: equal a/c0 characters do not identify
    # which holomorphic algebra object realizes a particular embedding.
    for n in range(order+1):
        combined = modules[0]['state_multiplicities'][n]
        if n:
            combined += modules[1]['state_multiplicities'][n-1]
            combined += 2*modules[2]['state_multiplicities'][n-1]
        assert combined == e8dims[n], ('E8 character identity',n)
    assert modules[2]['state_multiplicities'] == modules[3]['state_multiplicities']
    e8 = {'module':'E8','h':F(0), 'state_multiplicities':e8dims,
          'virasoro_primary_multiplicities_including_identity':primaries(e8dims,True,euler,part)}
    assert e8['virasoro_primary_multiplicities_including_identity'][:3] == [1,248,3875]
    return modules, e8


def spectrum(modules, delta_cut):
    sector_rows = []
    totals = defaultdict(lambda:[0,0])
    for row in modules:
        dims = row['state_multiplicities']
        ps = row['virasoro_primary_multiplicities_including_identity']
        for n,left in enumerate(dims):
            for m,right in enumerate(dims):
                delta, spin = 2*row['h']+n+m, n-m
                if delta > delta_cut:
                    continue
                states, primary = left*right, ps[n]*ps[m]
                sector_rows.append({'sector':row['module'],'left_grade':n,'right_grade':m,
                                    'h_left':row['h']+n,'h_right':row['h']+m,
                                    'Delta':delta,'spin':spin,'states':states,
                                    'Virasoro_primaries':primary})
                totals[delta,spin][0] += states
                totals[delta,spin][1] += primary
    rows = [{'Delta':d,'spin':s,'states':a,'Virasoro_primaries':b}
            for (d,s),(a,b) in sorted(totals.items())]
    for (d,s), counts in totals.items():
        assert totals[d,-s] == counts, ('parity',d,s)
        assert counts[0] >= counts[1] >= 0
        assert d >= abs(s), ('unitarity',d,s)
    assert totals[F(0),0] == [1,1]
    return sector_rows, rows, totals


def low_summary(diag, e8):
    relevant_scalar = [{'Delta':d, 'multiplicity':counts[1]}
                       for (d,s),counts in sorted(diag.items()) if s == 0 and 0 < d < 2]
    assert [(r['Delta'],r['multiplicity']) for r in relevant_scalar] == [
        (F(2,3),9),(F(10,13),25),(F(12,13),49),(F(14,13),169),
        (F(16,13),196),(F(4,3),729),(F(22,13),1764)]
    all_relevant = [{'Delta':d,'spin':s,'multiplicity':counts[1]}
                    for (d,s),counts in sorted(diag.items()) if 0 < d < 2 and counts[1]]
    assert sum(r['multiplicity'] for r in relevant_scalar) == 2941
    assert sum(r['multiplicity'] for r in all_relevant) == 10623
    assert diag[F(2),0] == [19558,19558]
    assert sum(c[0] for (d,s),c in diag.items() if d == 2) == 19798
    assert sum(c[1] for (d,s),c in diag.items() if d == 2) == 19784
    assert e8[F(2),0] == [61504,61504]
    assert sum(c[0] for (d,s),c in e8.items() if d == 2) == 69752
    assert not any(c[1] for (d,s),c in e8.items() if s == 0 and 0 < d < 2)
    return {'diagonal_U':{'relevant_scalar_primaries':relevant_scalar,
                          'relevant_scalar_components':2941,
                          'all_relevant_Virasoro_primaries':all_relevant,
                          'all_relevant_primary_components':10623,
                          'dimension_two_scalar_primaries':19558,
                          'dimension_two_scalar_extended_sector_tops':19522,
                          'dimension_two_U_current_bilinears':36,
                          'dimension_two_all_states':19798,
                          'dimension_two_all_Virasoro_primaries':19784,
                          'ordinary_primary_gap':F(2,3),'scalar_primary_gap':F(2,3),
                          'currents_each_chirality':6},
            'holomorphic_E8_full':{'ordinary_primary_gap':F(1),'scalar_primary_gap':F(2),
                                  'currents_each_chirality':248,
                                  'relevant_scalar_components':0,
                                  'dimension_two_scalar_primaries':61504,
                                  'dimension_two_all_states':69752,
                                  'first_chiral_H3_invariant_scalar_gap':F(2),
                                  'first_chiral_H3_invariant_dimension_two_scalars':6*248,
                                  'both_H3_times_H3op_invariant_scalar_gap':F(2),
                                  'both_H3_times_H3op_invariant_dimension_two_scalars':6*6,
                                  'invariant_action_scope':'For the selected canonical extension and first-factor action described in defects.tex, singlets are U tensor conjugate(Hprime). For both independent factors, singlets are U tensor conjugate(U).'},
            'scope':'Component multiplicities, not counts of extended-algebra sectors. Dimension two does not assert exact marginality. Invariant counts additionally use the selected canonical-extension defect action derived in defects.tex; characters alone do not determine that action.'}


def rounded(fn, direction):
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = direction
        return fn()


class Interval:
    """Closed Decimal interval; exp/ln widen their correctly rounded values."""
    def __init__(self, lo, hi=None):
        self.lo = D(lo)
        self.hi = D(lo if hi is None else hi)
        assert self.lo <= self.hi

    @classmethod
    def rational(cls, x):
        x = F(x)
        return cls(rounded(lambda:D(x.numerator)/D(x.denominator),ROUND_FLOOR),
                   rounded(lambda:D(x.numerator)/D(x.denominator),ROUND_CEILING))

    @staticmethod
    def coerce(x):
        return x if isinstance(x,Interval) else Interval.rational(x)

    def __add__(self, other):
        b = self.coerce(other)
        return Interval(rounded(lambda:self.lo+b.lo,ROUND_FLOOR),
                        rounded(lambda:self.hi+b.hi,ROUND_CEILING))
    __radd__ = __add__

    def __neg__(self):
        return Interval(self.hi.copy_negate(),self.lo.copy_negate())

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        b = self.coerce(other)
        pairs = [(x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return Interval(min(rounded(lambda:x*y,ROUND_FLOOR) for x,y in pairs),
                        max(rounded(lambda:x*y,ROUND_CEILING) for x,y in pairs))
    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.coerce(other)
        assert not b.lo <= 0 <= b.hi
        reciprocal = Interval(rounded(lambda:D(1)/b.hi,ROUND_FLOOR),
                              rounded(lambda:D(1)/b.lo,ROUND_CEILING))
        return self*reciprocal

    def exp(self):
        with localcontext() as ctx:
            ctx.prec = PREC
            return Interval(self.lo.exp().next_minus(),self.hi.exp().next_plus())

    def ln(self):
        assert self.lo > 0
        with localcontext() as ctx:
            ctx.prec = PREC
            return Interval(self.lo.ln().next_minus(),self.hi.ln().next_plus())

    def square(self):
        if self.lo >= 0 or self.hi <= 0:
            vals = [Interval(self.lo)*Interval(self.lo),Interval(self.hi)*Interval(self.hi)]
            return Interval(min(v.lo for v in vals),max(v.hi for v in vals))
        hi = max((Interval(self.lo)*Interval(self.lo)).hi,
                 (Interval(self.hi)*Interval(self.hi)).hi)
        return Interval(0,hi)


def pi_interval():
    # Exact parsing/addition at higher precision before directed 80-digit use.
    with localcontext() as ctx:
        ctx.prec = 110
        return Interval(D(PI_LO),D(PI_LO)+D('1e-100'))


def thermal_rows(rows):
    counts = defaultdict(int)
    for row in rows:
        counts[row['Delta']] += row['states']
    return sorted(counts.items())


def partial_moments(counts, beta):
    answer = [Interval(0),Interval(0),Interval(0)]
    for delta, count in counts:
        energy = delta-F(2,3)
        term = count*(-beta*energy).exp()
        answer[0] += term
        answer[1] += energy*term
        answer[2] += energy*energy*term
    return answer


def thermal_bounds(counts, cutoff, t, pi):
    """Z at b=2*pi*t; use modular invariance and all states Delta<=cutoff.

    For t>1, H(b) <= [L(b)-L(b')]/[exp((b-b')Ec)-1], b'=2*pi/t.
    For t=1, H(b) <= L'(b)/Ec.  For t<1 evaluate at 1/t.
    This is a theorem conditional on positivity and modular invariance of
    the full CFT, not a finite numerical proof of those premises.
    """
    tcold = max(t,1/t)
    b = 2*pi*tcold
    light = partial_moments(counts,b)
    ec = cutoff-F(2,3)
    if tcold == 1:
        bound = -light[1]/ec
        method = 'selfdual derivative: H <= L_prime/E_cut'
    else:
        bp = 2*pi/tcold
        dual_light = partial_moments(counts,bp)[0]
        numerator = light[0]-dual_light
        assert numerator.hi >= 0, 'modular positive-tail consistency'
        denominator = ((b-bp)*ec).exp()-1
        assert denominator.lo > 0
        bound = numerator/denominator
        method = 'modular heavy-tail inequality'
    assert bound.hi >= 0
    z = Interval(light[0].lo,(light[0]+Interval(0,bound.hi)).hi)
    return z, {'evaluated_t':tcold,'tail_upper_at_evaluated_t':bound.hi,'method':method}


def thermal_data(counts, cutoff):
    pi = pi_interval()
    results = []
    for t in (F(1,2),F(3,4),F(1),F(3,2),F(2)):
        b = 2*pi*t
        moments = partial_moments(counts,b)
        z, cert = thermal_bounds(counts,cutoff,t,pi)
        # Bound first and second tail moments using H(b0), b0=0.9b.
        t0 = F(9,10)*t
        b0 = 2*pi*t0
        z0, unused = thermal_bounds(counts,cutoff,t0,pi)
        l0 = partial_moments(counts,b0)[0]
        h0upper = max(D(0),(z0-l0).hi)
        delta = (b-b0).lo
        ec = cutoff-F(2,3)
        ec_interval = Interval.rational(ec)
        tail = []
        for k in (1,2):
            if (Interval(delta)*ec_interval).lo >= k:
                factor = (ec_interval if k == 1 else ec_interval.square())*(-Interval(delta)*ec).exp()
            else:
                peak = Interval(k)/Interval(delta)
                factor = (peak if k == 1 else peak.square())*Interval(-k).exp()
            tail.append((factor*Interval(h0upper)).hi)
        m1 = Interval(moments[1].lo,(moments[1]+Interval(0,tail[0])).hi)
        m2 = Interval(moments[2].lo,(moments[2]+Interval(0,tail[1])).hi)
        energy = m1/z
        if t == 1:
            assert energy.lo <= 0 <= energy.hi
            energy = Interval(0)  # Exact consequence of Z(b)=Z(4pi^2/b).
        variance_raw = m2/z-energy.square()
        assert variance_raw.hi >= 0
        variance = Interval(max(D(0),variance_raw.lo),variance_raw.hi)
        entropy = z.ln()+b*energy
        results.append({'t_beta_v_over_L':t,'b':b,'Z':z,'log_Z':z.ln(),
                        'free_energy_in_units_2pi_v_over_L':-z.ln()/b,
                        'mean_Delta_minus_2_over_3':energy,
                        'heat_capacity':b.square()*variance,
                        'entropy':entropy,
                        'partial_Z_at_requested_t':moments[0],
                        'modular_tail_certificate':cert,
                        'moment_tail_certificate':{'t0':t0,'H_at_t0_upper':h0upper,
                                                   'first_moment_tail_upper':tail[0],
                                                   'second_moment_tail_upper':tail[1]}})
    return results


def write_json(path, value):
    with path.open('x',encoding='utf-8') as stream:
        json.dump(value,stream,indent=2,default=encode)
        stream.write('\n')


def write_tsv(path, fields, rows):
    with path.open('x',encoding='utf-8') as stream:
        stream.write('\t'.join(fields)+'\n')
        for row in rows:
            stream.write('\t'.join(str(row[key]) for key in fields)+'\n')


def write_readable_thermal(path, thermal):
    """Each displayed rounded number encloses its rigorous interval within 1e-6."""
    with path.open('x',encoding='utf-8') as stream:
        stream.write('\\begin{tabular}{c|c|rrrr}\n')
        stream.write('theory & $t$ & $Z$ & $\\langle\\Delta-2/3\\rangle$ & $C_V$ & $S$\\\\\\hline\n')
        for name,records in thermal.items():
            label = '$U$ diagonal' if name == 'diagonal_U' else '$E_8$ full'
            for row in records:
                values = []
                for key in ('Z','mean_Delta_minus_2_over_3','heat_capacity','entropy'):
                    interval = row[key]
                    with localcontext() as ctx:
                        ctx.prec = PREC
                        center = ((interval.lo+interval.hi)/2).quantize(D('0.000001'))
                        assert center-D('0.000001') < interval.lo <= interval.hi < center+D('0.000001')
                    values.append(format(center,'f'))
                stream.write(label+' & $'+str(row['t_beta_v_over_L'])+'$ & '+' & '.join(values)+'\\\\\n')
        stream.write('\\end{tabular}\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=24)
    parser.add_argument('--delta-cut',type=int,default=24)
    parser.add_argument('--outdir',type=Path,required=True)
    parser.add_argument('--skip-thermal',action='store_true')
    args = parser.parse_args()
    if not 4 <= args.delta_cut <= args.order <= 64:
        parser.error('require 4 <= delta-cut <= order <=64')
    as_limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    if as_limit == resource.RLIM_INFINITY or as_limit > 6*1024**3:
        parser.error('a finite address limit <=6 GiB is mandatory; use hi_cft_safe_run.py')
    out = args.outdir.resolve()
    out.mkdir(parents=True,exist_ok=True)
    names = ['characters.json','characters.tsv','fundamental_matrix.json',
             'diagonal_sector_spectrum.tsv','diagonal_spectrum.tsv','e8_spectrum.tsv',
             'scalars.tsv','low_spectrum.json','thermal.json','thermal.tsv','thermal_readable.tex','run_summary.json']
    if any((out/name).exists() for name in names):
        parser.error('refusing to overwrite any dataset output; choose a fresh outdir')
    started = monotonic()
    x,f,g,e4 = xi_coefficients(args.order)
    modules,e8 = chiral_data(args.order,x,e4)
    dsector,drows,dtotals = spectrum(modules,args.delta_cut)
    unused,erows,etotals = spectrum([e8],args.delta_cut)
    low = low_summary(dtotals,etotals)
    character_doc = {'schema':'haagerup-c8-characters-v1','source_url':SOURCE_URL,
                     'source_location':'Sections 1.4 and 2.4; equations (1.24), (2.7)',
                     'gamma':0,'c_left':8,'c_right':8,'chiral_grade_max':args.order,
                     'coefficient_convention':'chi_i=q^(h_i-1/3) sum_n a_i[n] q^n; n is grade above actual ground',
                     'modules':modules,'holomorphic_E8':e8,
                     'E8_character_identity':'chi_E8=chi_0+chi_b+2chi_a=chi_0+chi_b+2chi_c0; scalar equality does not choose an extension algebra',
                     'Virasoro_convention':'Including identity once. Nonvacuum P_i=Euler*a_i; vacuum P_0=Euler*a_0+q. Unitary c=8 has no positive-h Verma nulls.',
                     'scope':'Exact formal coefficients. Interpretation uses the manuscript construction and character identification. Finite positivity is checked only through the stated grade.'}
    write_json(out/'characters.json',character_doc)
    write_json(out/'fundamental_matrix.json',{'Lambda':LAM,'chi':CHI,
        'Xi_coefficient_convention':'Xi=q^Lambda sum_(n>=-1) Xi_n q^n',
        'Xi':{str(n):matrix for n,matrix in x.items()},'f':f,'g':g,
        'differential_equation':'q*dXi/dq=Xi*[f*(Lambda-I)+g*(chi+[Lambda,chi])]',
        'recurrence':'(n+1+lambda_i-lambda_j) Xi_n[i,j]=sum_(r=1)^(n+1) [f_r(lambda_j-1)Xi_(n-r)[i,j]+g_r(Xi_(n-r)C)[i,j]]'})
    crows = []
    for row in modules+[e8]:
        for n,(a,p) in enumerate(zip(row['state_multiplicities'],row['virasoro_primary_multiplicities_including_identity'])):
            crows.append({'module':row['module'],'grade':n,'h':row['h']+n,
                          'states':a,'Virasoro_primaries':p})
    write_tsv(out/'characters.tsv',['module','grade','h','states','Virasoro_primaries'],crows)
    write_tsv(out/'diagonal_sector_spectrum.tsv',
              ['sector','left_grade','right_grade','h_left','h_right','Delta','spin','states','Virasoro_primaries'],dsector)
    fields = ['Delta','spin','states','Virasoro_primaries']
    write_tsv(out/'diagonal_spectrum.tsv',fields,drows)
    write_tsv(out/'e8_spectrum.tsv',fields,erows)
    scalar_rows = [dict(theory=name,**row) for name,rows in [('diagonal_U',drows),('E8_full',erows)]
                   for row in rows if row['spin'] == 0]
    write_tsv(out/'scalars.tsv',['theory']+fields,scalar_rows)
    write_json(out/'low_spectrum.json',low)
    thermal = None
    if not args.skip_thermal:
        thermal = {name:thermal_data(thermal_rows(rows),F(args.delta_cut))
                   for name,rows in [('diagonal_U',drows),('E8_full',erows)]}
        write_json(out/'thermal.json',{'schema':'haagerup-c8-thermal-intervals-v1',
            'exact_cutoff_Delta':args.delta_cut,'decimal_precision':PREC,
            'pi_lower':PI_LO,'pi_upper_minus_lower':'1e-100',
            'normalization':'Z=Tr exp[-2*pi*(beta*v/L)*(Delta-2/3)]; heat capacity and entropy use k_B=1',
            'scope':'Conditional certified intervals using exact low states, positive omitted degeneracies, full modular invariance, a fixed pi enclosure, and outward Decimal rounding. No claim that finitely many coefficients prove a CFT or modular invariance.',
            'theories':thermal})
        trows = []
        for name,records in thermal.items():
            for row in records:
                new = {'theory':name,'t':row['t_beta_v_over_L']}
                for observable in ('Z','log_Z','free_energy_in_units_2pi_v_over_L',
                                   'mean_Delta_minus_2_over_3','heat_capacity','entropy'):
                    new[observable+'_lower'] = row[observable].lo
                    new[observable+'_upper'] = row[observable].hi
                trows.append(new)
        write_tsv(out/'thermal.tsv',list(trows[0]),trows)
        write_readable_thermal(out/'thermal_readable.tex',thermal)
    source_paths = [Path(__file__).resolve(),ROOT/'hi_cft_third_flavoured_trace_check.py',
                    ROOT/'hi_cft_third_rank3_current_series.py',
                    ROOT/'hi_cft_20260923_next_structure_conditional_characters.md']
    checks = {'published_first_four_columns':True,'all_reported_character_coefficients_nonnegative_integral':True,
              'all_reported_Virasoro_multiplicities_nonnegative_integral':True,
              'all_chiral_descendant_reconstructions':True,'independent_E8_eta_product_identity':True,
              'spin_reflection_and_unitarity':True,'explicit_low_spectrum_controls':True,
              'thermal_interval_consistency':None if args.skip_thermal else True}
    outputs = {name:sha(out/name) for name in names if (out/name).is_file()}
    summary = {'status':'PASS','schema':'haagerup-c8-physics-spectrum-v1','order':args.order,
               'complete_full_CFT_Delta_max':args.delta_cut,'characters':len(modules),
               'character_rows_including_E8':len(crows),'diagonal_sector_rows':len(dsector),
               'diagonal_Delta_spin_rows':len(drows),'E8_Delta_spin_rows':len(erows),
               'checks':checks,'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in source_paths},
               'output_sha256':outputs,'elapsed_seconds':monotonic()-started,
               'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               'scope':'Arithmetic consequences of published modular data and manuscript character identification. No lattice modes, OPE coefficients, defect eigenvectors, existence proof, or Lean proof are computed.'}
    write_json(out/'run_summary.json',summary)
    print(json.dumps(summary,indent=2,default=encode))


if __name__ == '__main__':
    main()
