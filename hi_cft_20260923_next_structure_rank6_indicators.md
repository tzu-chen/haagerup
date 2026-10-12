# Rank-six higher multiplicity: audited indicator exclusion

**Status, 2026-09-23:** independently audited by root and exact_grade4.
Both reviewers checked the induction, both moments, squareclass bound,
conductor-40 orbit calculation, and equality contradiction. Their common
correction was to require that the squared sum lie in Q(sqrt(10)) in the
equality lemma; this is now explicit and follows from (3.2). No numerical
calculation has been run for this note. A pseudounitary categorification
of the noncommutative ring below, with untwisted pointed subcategory,
must have multiplicity one.

## 1. Hypotheses and source inputs

Let C be a pseudounitary fusion category with simples

    1, a, a^2, r_0=r, r_1=ar, r_2=a^2r,

and fusion rules

    a^3=1,  r a=a^2 r,
    r_i r_j=a^(i-j)+m(r_0+r_1+r_2),  m>=1.

Assume the pointed subcategory is tensor equivalent to ordinary Vec(Z3),
with its canonical positive spherical structure. In the VOA application this
untwisted condition was established separately through the pointed category
of B and its holomorphic extension.

Set R=r_0+r_1+r_2 and

    d=(3m+sqrt(9m^2+4))/2,  d^2=1+3md,
    s=1+d^2=2+3md,  Dim(C)=3s,  Delta=9m^2+4.

Primary theorem inputs:

* Ostrik, *Pivotal fusion categories of rank 3*, Theorems 2.5 and 2.13:
  induction of the unit, its twist, and the formal-codegree correspondence.
  [Primary paper](https://arxiv.org/abs/1309.4822).
* Ng--Schauenburg, *Frobenius-Schur indicators and exponents of spherical
  categories*, Theorem 4.1: the center-twist formula
  `Tr(theta^k on I(V)) = Dim(C) nu_k(V)`.
  The theorem and numbering were checked directly in arXiv v3, page 10;
  [primary paper](https://arxiv.org/pdf/math/0601012).
* The finite-order rotation definition gives nu_1(r)=0 and
  nu_2(r)=epsilon in {+1,-1}. Untwisted Vec(Z3) gives nu_3(a)=1.
* Larson, *Pseudo-unitary non-self-dual fusion categories of rank 4*,
  Theorem 1.3 (= the section-6 root-count theorem): if N roots of unity
  sum to A+B sqrt(D), for integral A,B and squarefree D>0, then
  `N >= |B| phi(2D)`.
  [Primary paper](https://arxiv.org/pdf/1401.1879).
  For half-integral A,B apply this theorem to two copies of the multiset.

All uses of pseudounitarity below mean the canonical positive spherical
structure. No unitarizability assumption is used.

## 2. Exact center induction

Write F:Z(C)->C for forgetful and I for its adjoint. We use

    F I(v) = sum_x x v x*,
    Hom(I(v),I(w)) = Hom(v,F I(w)).

The complex fusion algebra has irreducibles chi_+, chi_- and pi, of
dimensions 1,1,2 respectively:

    chi_+(a)=chi_-(a)=1,
    chi_+(r)=d, chi_-(r)=-1/d,
    pi(a)=diag(zeta3,zeta3^2), pi(r)=[[0,1],[1,0]].

Their formal codegrees are

    3s, 3s/d^2, 3.

Consequently

    I(1) = 1 + X + 2Y,
    dim X=d^2, dim Y=s,
    theta_X=theta_Y=1.

Every F(Z), for Z central, is invariant under conjugation by a. Since
conjugation cycles the three r_i, their multiplicities in F(Z) coincide.
Also

    F I(1)=6*1+3m R.

The formal-codegree multiplicity theorem and dimensions therefore give

    F(X)=1+mR,   F(Y)=2*1+mR.

For a nonidentity invertible,

    F I(a)=F I(a^2)=3a+3a^2+3mR.

Thus I(a) and I(a^2) have norm squared 3 and mutual inner product 3,
and are equal, multiplicity-free sums of three distinct simples C_0,C_1,C_2.
They do not overlap I(1). Each C_j has exactly one copy of a and of a^2,
so

    F(C_j)=a+a^2+b_j R,  b_j>=0,  sum b_j=3m.

The trace formula for nu_3(a)=1 gives

    sum_j dim(C_j) theta_j^3 = Dim(C) = sum_j dim(C_j).

Since dimensions are positive and twists are roots of unity, equality in
the triangle inequality forces theta_j^3=1 for every j. The nu_1(a)=0
formula gives

    0=sum_j (2+3b_j d) theta_j.

The real quadratic field Q(d) and Q(zeta3) are linearly disjoint. Splitting
the last equation gives sum theta_j=0 and sum b_j theta_j=0. Hence the
three twists are 1,zeta3,zeta3^2 once each and all b_j=m. In particular

    dim(C_j)=s.

Every remaining central simple Z_j has no invertible summands in F(Z_j),
because all I(1),I(a),I(a^2) summands have now been exhausted. Therefore

    F(Z_j)=n_j R,  n_j>=1,  dim Z_j=3n_j d.

Comparing global dimensions of Z(C) and C gives

    9s^2 = 1+d^4+4s^2 + 9d^2 sum_j n_j^2,
    sum_j n_j^2=4m^2+2.                           (2.1)

The same identity follows from the decomposition of I(r), which is

    I(r)=mX+mY+m(C_0+C_1+C_2)+sum_j n_j Z_j.

## 3. Two exact root-sum identities

Let theta_j denote the twist of Z_j and epsilon=nu_2(r)=+/-1. Because
the three C twists sum to zero, as do their squares, the first two
indicator formulas give

    sum_j n_j^2 theta_j
      = -(m^2+m sqrt(Delta))/2,                  (3.1)

    sum_j n_j^2 theta_j^2
      = [-m^2+(2epsilon-m)sqrt(Delta)]/2.        (3.2)

For example the k=1 equation before simplification is

    0=m(d^2+s)+3d sum_j n_j^2 theta_j.

For k=2 the right side becomes 3s epsilon. Using 1/d=d-3m gives
(3.1)--(3.2). The root multiset here literally repeats theta_j exactly
n_j^2 times, so its number of roots is the integer

    N=4m^2+2.

No assertion that the Z_j have distinct twists or that n_j=1 is needed.

## 4. All squareclasses other than 10 are excluded for m>1

Write Delta=t^2 D with D squarefree and t positive integral. Delta is
nonsquare for m>=1 because (3m)^2 < Delta < (3m+1)^2. Also:

* 3 does not divide Delta, and Delta=1 mod 3; hence D=1 mod 3.
* 7 does not divide Delta: otherwise m^2=5 mod 7, impossible.

For squarefree D satisfying these properties, D!=10 implies

    phi(2D)/sqrt(D) >= 12/sqrt(13).             (4.1)

Here is an elementary proof. For odd squarefree D the ratio is the product
of (p-1)/sqrt(p) over its prime divisors. Every divisor is at least 5,
and 7 is excluded. With one prime, the condition D=1 mod 3 forces p>=13.
With two or more odd primes the product is at least
40/sqrt(55)>12/sqrt(13), and extra factors exceed one. For even D the
ratio is sqrt(2) times the corresponding odd-prime product. With one odd
prime p, D=1 mod3 forces p=2 mod3; p=5 gives D=10 and otherwise p>=11,
yielding sqrt(2)*10/sqrt(11)>12/sqrt(13). Two or more odd primes give an
even larger product. D=1,2 are excluded already.

Larson's theorem applied to two copies of (3.1) gives

    N >= (mt/2) phi(2D)
      >= 6m sqrt(9m^2+4)/sqrt(13).

For m>1 this is strictly larger than 4m^2+2, since the difference of
the squares after clearing denominator 13 is

    36m^2(9m^2+4)-13(4m^2+2)^2
      =4(m^2-1)(29m^2+13)>0.

Thus m>1 requires D=10.

## 5. A sharper root-count lemma for Q(sqrt(10))

**Lemma (including equality).** Suppose a,b are nonnegative integers and
a multiset of N roots of unity has sum -a-b sqrt(10). Then N>=a+8b.
If equality holds **and the sum of squared roots belongs to Q(sqrt(10))**,
then its sum of squared roots is a. The extra hypothesis is provided by
(3.2) in the application.

Proof. Choose a cyclotomic field Q(zeta_L) containing all the roots and
Q(sqrt(10)), whose quadratic conductor is 40. Apply every automorphism in
G=Gal(Q(zeta_L)/Q(sqrt(10))) to the entire multiset, and take the union of
these multisets. If M=|G|, the new multiset has exactly MN roots, sum
M(-a-b sqrt(10)), and integral, nonnegative multiplicities constant on G
orbits. Its sum of squared roots is the Galois trace of the original
squared sum, hence M times that sum under the stated additional
hypothesis. There is no division of multiplicities in this argument.

For a primitive root of order Y, two cases occur.

1. If 40 does not divide Y, the intersection Q(zeta_Y) cap Q(sqrt(10))
   is Q. Its orbit is the full primitive-Y orbit, sum mu(Y) in {0,+1,-1},
   with phi(Y) members. Thus its length is at least the absolute value of
   its rational sum. Equality for a negative rational contribution can
   occur only at Y=2, the singleton {-1}.

2. If 40 divides Y, the primitive-Y roots split into the two orbits
   distinguished by the primitive real quadratic character chi_40. Their
   sums are

       (c_Y(1) +/- tau_Y(chi_40))/2.

   Since 8 divides Y, c_Y(1)=mu(Y)=0. The induced quadratic Gauss sum is
   zero unless Y=40u, with u squarefree and coprime to 40; in the latter
   case it is mu(u)chi_40(u) sqrt(40). Each orbit therefore has sum zero
   or +/-sqrt(10), and length phi(Y)/2 >= 8. Equality for a nonzero
   quadratic contribution requires Y=40: if u>1 and coprime to 40 then
   phi(u)>=2, while additional prime powers produce zero sum or increase
   the orbit size.

The rational part -Ma requires at least Ma roots in type 1, and the
quadratic coefficient -Mb requires at least 8Mb roots in type 2. These
disjoint costs establish MN>=M(a+8b).

Under equality, no zero orbit or cancellation is possible. The averaged
multiset consists of Ma copies of {-1} and Mb copies of the negative
primitive-40 orbit (of size eight). Every primitive-40 orbit has squared
sum zero. Indeed, reduction of its exponents modulo 20 runs once through
the units modulo 20: chi_40(x+20)=-chi_40(x). Its squared sum is therefore
the Ramanujan sum c_20(1)=mu(20)=0. The averaged squared sum is Ma, and
division by M proves the original squared sum is a. QED.

The imprimitive Gauss-sum formula is Montgomery--Vaughan,
*Multiplicative number theory I*, Theorem 9.10; the authors' chapter is
[available here](https://personal.science.psu.edu/rcv4/568s20/568chapter9.pdf).
It can also be obtained directly by Chinese remaindering the 2-power,
5-power, and prime-to-10 factors. Both reviewers independently checked
the formula and its zero cases in this application.

## 6. Exclusion of D=10 and m>1

The equation 9m^2+4=10t^2 forces m,t even, by reduction modulo 4.
Thus in (3.1),

    a=m^2/2, b=mt/2

are integers. The preceding lemma implies

    4m^2+2 >= m^2/2+4mt.                       (6.1)

For m>=4, t/m=sqrt(9/10+2/(5m^2))>sqrt(9/10)>15/16,
so the right side exceeds (1/2+15/4)m^2=(17/4)m^2,
which is greater than 4m^2+2 for m>=4. This is impossible.

The sole remaining possibility is m=2,t=2. Here N=18 and a+8b=2+16=18.
Equation (3.2) puts the squared sum in Q(sqrt(10)), so the equality
conclusion of the lemma applies and forces

    sum_j n_j^2 theta_j^2=2.

But (3.2) gives -2 for epsilon=+1, and -2-4sqrt(10) for epsilon=-1.
Both contradict 2.

**Conclusion:** under the stated pseudounitary and untwisted
pointed hypotheses, m=1 is the only possible positive multiplicity.
The actual existence and equivalence classes at m=1 are separate issues.

## 7. Positivity tests that do not help

The HLPW primary-3 criterion is automatic for this entire ring family.
Using the irreducible representations in section 2, the blocks of
sum_b pi_1(b) tensor pi_2(b) tensor pi_3(b)/FPdim(b) are:

* No two-dimensional factor: 3+3(-1)^j d^(2-2j), j=0,1,2,3.
* One two-dimensional factor: zero.
* Two: nonzero eigenvalues 3(1+/-c/d), with c=d or -1/d.
* Three: nonzero eigenvalues 3(1+/-1/d).

All are nonnegative. HLPW Theorem 3.9 makes this equivalent to all the
primary-n tests. Thus this criterion cannot justify m=1.
[Primary paper](https://arxiv.org/pdf/2210.00792).

The rank-four near-group classification and the standard-model character
exclusions remain logically separate. This argument addresses the
noncommutative rank-six fusion ring only.
