# Conditional rank-twelve center after the multiplicity exclusion

This applies to the rank-six alternative in
`hi_cft_20260923_next_structure_rank46.md`. The independently audited
`next_structure_rank6_indicators.md` proves that its multiplicity is one.
Properness and exclusion of the remaining rank-four alternatives are separate
questions.

Put d=(3+sqrt(13))/2 and s=1+d^2. The six known central objects from the
induction calculation have dimensions

    1, d^2, s, s, s, s

and twists 1,1,1,1,zeta_3,zeta_3^2. The remaining objects have dimensions
3 n_j d, with positive integral n_j, and satisfy

    sum n_j^2 = 6,
    sum n_j^2 theta_j = (-1-sqrt(13))/2.

We can already recover their number and twists without a classification
of categorifications. Take a cyclotomic field containing the roots and
Q(sqrt(13)), and take the union of the root multiset over its Galois group
over Q(sqrt(13)). This multiplies both cardinality and sum by the same
positive integer. Each Galois orbit contributing a nonzero sqrt(13)
coefficient has size at least six. The induced quadratic Gauss-sum formula
shows its coefficient has absolute value at most 1/2. Equality between the
available six roots and the required coefficient 1/2 therefore allows only
the minimal orbits, of orders 13 or 26, with negative quadratic coefficient.
Their sums are respectively (-1-sqrt(13))/2 and (1-sqrt(13))/2. The rational
part of the required sum excludes order 26 and leaves no other roots.

Thus every original root is a primitive thirteenth root with nonresidue
exponent. The six roots in this half-orbit are linearly independent over Q:
any relation among them gives a polynomial of degree at most twelve,
with zero constant term, divisible by Phi_13, and hence is zero. Comparing
with the quadratic period proves that each occurs once. Consequently
n_j=1 for exactly six distinct objects, with twist exponents

    {2,5,6,7,8,11}/13.

Multiplication of these exponents by two gives the residue half-orbit.
The second moment is therefore (-1+sqrt(13))/2; the second-indicator
formula in the preceding note forces nu_2(rho)=+1.

In particular the center has rank twelve, dimensions

    1, d^2, s (four times), 3d (six times),

and the usual Haagerup twist spectrum. For c=8 the character T matrix is
the displayed categorical twist matrix multiplied by exp(-2 pi i/3).

The complete modular data now follow from Gannon--Schopieray--Yadav,
Theorem A(2), equivalently Theorem 5.1. Its stated assumptions here are
complex spherical and untwisted; this part does not require a C* structure
or a separable algebra 1+rho. The metric group has order 13, so it is
Z/13 with q(h)=s_0 h^2/13 and s_0 a quadratic nonresidue. Its isometry
class is unique. Thus their smashed-sum data are precisely the standard
Haagerup modular data. This conclusion identifies S and T, not a braided
equivalence solely from modular data. Their stronger categorification
enumeration has a Q-system-type scope which must not be silently added.

Primary source: [Gannon--Schopieray--Yadav, On Haagerup--Izumi fusion
categories, Theorem A(2) and Section 5](https://arxiv.org/html/2609.25185v1).
The quadratic-period argument above is our direct specialization of the
induced Gauss-sum orbit argument already used in the audited indicator note.
