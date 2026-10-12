# Independent root audit of the rank-six indicator argument

23 September 2026. This is a reading and algebra audit, with no numerical
job. The audited argument is in
`hi_cft_20260923_next_structure_rank6_indicators.md`.

The conclusion passes: a pseudounitary categorification of

    a^3=1, ar=ra^2, r^2=1+m(r+ar+a^2r), m>=1,

whose pointed subcategory is untwisted Vec(Z3), must have m=1.
This is conditional on this fusion-ring branch. It does not prove the
candidate VOA proper or eliminate its rank-four branch.

I independently recomputed the following steps.

* The complex fusion algebra has irreducible dimensions 1,1,2 and
  formal codegrees 3s,3s/d^2,3, where d^2=1+3md and s=1+d^2.
  Hence I(1)=1+X+2Y, with dimensions 1,d^2,s. Conjugation by a
  cycles the noninvertibles, giving F(X)=1+mR and F(Y)=2+mR.
* FI(a)=FI(a^2)=3a+3a^2+3mR. Its norm and mutual inner product
  force three shared, multiplicity-one central summands. The untwisted
  hypothesis gives nu_3(a)=1, so their twists are cube roots. The first
  indicator then forces exactly 1,zeta_3,zeta_3^2 and equal dimensions s.
* Every other central simple forgets to n_j R. Global dimension gives
  sum n_j^2=4m^2+2. Applying the first and second indicators to r gives

      sum n_j^2 theta_j = -(m^2+m sqrt(9m^2+4))/2,
      sum n_j^2 theta_j^2 = [-m^2+(2epsilon-m)sqrt(9m^2+4)]/2,

  where epsilon=+1 or -1. The roots are counted with the actual integer
  multiplicities n_j^2.
* For squarefree D in 9m^2+4=t^2D, the stated elementary lower bound
  phi(2D)/sqrt(D)>=12/sqrt(13) holds unless D=10. Larson's bound then
  contradicts m>1. The cleared squared difference is exactly
  4(m^2-1)(29m^2+13).
* In Q(sqrt(10)), Galois averaging gives the sharper root count
  N>=a+8b for a sum -a-b sqrt(10). Primitive orders not divisible by
  40 contribute only integral Ramanujan sums; orders divisible by 40
  contribute zero or a signed sqrt(10), at cost at least eight roots.
  The imprimitive Gauss sum has nonzero contribution only for order
  40u with u squarefree and coprime to 40. Equality permits only -1
  and the negative quadratic orbit of primitive fortieth roots.

An important correction was made during audit: averaging the squared
sum gives M times the original squared sum only if that sum belongs to
Q(sqrt(10)). The general lemma now states this extra hypothesis. It is
available here from the second indicator identity. The squared sum of
either primitive-40 quadratic orbit is zero, since its exponents reduce
once to the units modulo 20 and mu(20)=0. Equality therefore forces
the original squared sum to be a.

The remaining Pell squareclass has even m,t. Its root-count inequality
excludes m>=4; at m=t=2, equality forces squared sum +2, whereas the
indicator gives -2 or -2-4sqrt(10). Thus all m>1 are excluded.

Primary theorem statements checked directly:

* [Ostrik, Proposition 2.4 and Theorems 2.5, 2.13](https://arxiv.org/html/1309.4822)
  for induction, unit twists, and formal codegrees.
* [Ng--Schauenburg, Theorem 4.1](https://arxiv.org/html/math/0601012)
  for the center-twist indicator formula.
* [Larson, Theorem 1.3](https://arxiv.org/html/1401.1879)
  for the number of roots required for a quadratic irrational sum.

The separate exact-grade agent independently checked the induction and
arithmetic and found the same necessary correction, then accepted the
corrected argument. No unitarizability theorem or classification of all
C*-fusion categories is used in this exclusion.
