"""Shared exact gamma0 next-grade trace coefficients and affine descendants.

Pure stdlib, imported only by ROOT's bounded certificate jobs. No numerical
job or alteration of the published-matrix producer is performed here.
"""
from fractions import Fraction as F
from hi_cft_third_flavoured_trace_check import CHI,LAMBDA,NAMES


# EG's unnumbered Haagerup expansion after(2.7), gamma=0. For the vacuum
# these are grades1 and2, because its separate polar term is grade0.
C0 = tuple(int(CHI[i][0]) for i in range(12))
C1 = (120,1250,1377,1377,243,594,292,777,1623,229,347,441)
LEADING_FORMS = (
    (4,-9,-1,-3),(20,-9,1,3),(18,9,0,0),(18,9,0,0),
    (0,1,0,0),(6,-6,0,0),(0,0,1,0),(10,0,1,-4),
    (30,0,0,9),(0,0,0,1),(4,0,-1,-3),(2,0,-1,2))


def coefficient_forms():
    """Each row multiplies(level,t_c1,t_d1,t_d4), ordinary index units."""
    base0 = [(F(1,12)+lam/4)*count-2*(i == 0)
        for i,(lam,count) in enumerate(zip(LAMBDA,C0))]
    base1 = [(F(1,12)+(lam+1)/4)*C1[i]-2*C0[i]-6*(i == 0)
        for i,lam in enumerate(LAMBDA)]
    forms = []
    for i in range(12):
        row = [sum((CHI[i][j]+240*(i == j))*LEADING_FORMS[j][a] for j in range(12)) for a in range(4)]
        row[0] += base1[i]-sum((CHI[i][j]+240*(i == j))*base0[j] for j in range(12))
        forms.append(tuple(map(F,row)))
    if forms[NAMES.index('c1')] != tuple(map(F,(72,12,0,0))):
        raise AssertionError('Independent c1 next-grade derivation failed')
    return {'basis_variables':('level','t_c1','t_d1','t_d4'),
        'leading_nonpolar_dimensions':dict(zip(NAMES,C0)),
        'next_dimensions':dict(zip(NAMES,C1)),
        'leading_forms':dict(zip(NAMES,LEADING_FORMS)),
        'next_forms':dict(zip(NAMES,forms)),
        'particular_leading_coefficients':dict(zip(NAMES,base0)),
        'particular_next_coefficients':dict(zip(NAMES,base1)),
        'vacuum_grade_scope':'Vacuum next-form means grade2 (dimension120), not grade1. Every nonvacuum next-form means grade1 above its ground.',
        'formula':'H_next=(CHI+240I)v; Qpart_next_i=(1/12+(Lambda_i+1)/4)C1_i-2C0_i-6delta_i0'}


def evaluate(form,level,a,b,c):
    return sum((x*y for x,y in zip(form,(level,a,b,c))),F(0))


def index(n):
    if type(n) is not int or n < 1:
        raise ValueError('Positive integer SU2 dimension required')
    return n*(n*n-1)//6


def affine_grade_one(terms,k,l=None):
    """Exact generated affine grade1; terms are(n,m,multiplicity).

    l=None means only the first SU2 factor is included; m is a passive
    multiplicity dimension. No coset-descendant state is added.
    """
    if type(k) is not int or k < 1 or l is not None and (type(l) is not int or l < 1):
        raise ValueError('Positive affine levels required')
    dimension,left,right = 0,0,0
    nulls = []
    for n,m,count in terms:
        if type(count) is not int or count < 1 or n > k+1 or l is not None and m > l+1:
            raise ValueError('Invalid integrable ground term')
        il,ir = m*index(n),n*index(m)
        if l is None:
            d,tl,tr = 3*n*m,3*il+4*n*m,3*ir
        else:
            d,tl,tr = 6*n*m,6*il+4*n*m,6*ir+4*n*m
        if n == k+1:
            d -= (n+2)*m
            tl -= m*index(n+2)
            tr -= (n+2)*index(m)
            nulls.append({'side':'left','ground_dimensions':[n,m],
                'null_dimensions':[n+2,m],'multiplicity':count})
        if l is not None and m == l+1:
            d -= n*(m+2)
            tl -= (m+2)*index(n)
            tr -= n*index(m+2)
            nulls.append({'side':'right','ground_dimensions':[n,m],
                'null_dimensions':[n,m+2],'multiplicity':count})
        dimension += count*d
        left += count*tl
        right += count*tr
    if min(dimension,left,right) < 0:
        raise AssertionError('Affine descendant dimension/index became negative')
    return {'dimension':dimension,'left_index':left,'right_index':right,
        'grade_one_integrable_nulls':nulls,
        'scope':'Only the mandatory affine-generated grade1 is counted. No complementary Virasoro descendant or extra affine-primary multiplicity is assumed.'}


def vacuum_grade_two(k,l):
    """Vacuum affine product grade2 from g_-2 plus Sym2(g_-1)."""
    return {'dimension':27-5*(k == 1)-5*(l == 1),
        'left_index':36-20*(k == 1),'right_index':36-20*(l == 1),
        'scope':'The only vacuum grade2 integrable null is the spin2 irrep when its SU2 level is1.'}


def selftest():
    data = coefficient_forms()
    cases = 0
    for k in range(1,8):
        for l in range(1,8):
            for n in range(1,min(7,k+1)+1):
                for m in range(1,min(7,l+1)+1):
                    reps = []
                    for r in range(abs(n-3)+1,n+3,2):
                        if not(n == k+1 and r == n+2):reps.append((r,m))
                    for s in range(abs(m-3)+1,m+3,2):
                        if not(m == l+1 and s == m+2):reps.append((n,s))
                    exact = (sum(a*b for a,b in reps),sum(b*index(a) for a,b in reps),sum(a*index(b) for a,b in reps))
                    got = affine_grade_one([(n,m,1)],k,l)
                    if exact != (got['dimension'],got['left_index'],got['right_index']):
                        raise AssertionError('Clebsch-Gordan affine-grade1 check failed')
                    cases += 1
    for k,l in ((1,1),(1,2),(2,1),(2,2)):
        row = affine_grade_one([(1,1,1)],k,l)
        if (row['dimension'],row['left_index'],row['right_index']) != (6,4,4):
            raise AssertionError('Vacuum grade1 current normalization failed')
    return {'affine_grade_one_Clebsch_Gordan_cases':cases,
        'vacuum_grade_one_normalization_checked':True,
        'independent_c1_next_form_checked':True}
