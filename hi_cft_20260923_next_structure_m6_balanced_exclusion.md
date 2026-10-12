# Excluding the balanced Z3+6 induction pattern by Verlinde integrality

Status: independently audited by exact_grade4; root audit requested.
No numerical job was run. This argument needs pseudounitarity, not a C*
structure, and excludes the p=q=1 pattern in the center induction data.

Let F have near-group fusion rules Z3+6. Put

    d=3+2 sqrt(3), r=1+d=4+2 sqrt(3), s=2r.

Its dimension is 3+d^2=6r. Larson's center-induction calculation
(Propositions 4.3--4.7 and Corollary 4.8) gives the alternatives
p+q=2. In the balanced case p=q=1, the central simples and dimensions are

| Objects | Dimensions | Number |
|---|---:|---:|
| 1 | 1 | 1 |
| X | 1+2d=7+4 sqrt(3) | 1 |
| Y,Y',C | s=2r | 3 |
| D,E,D',E' | r | 4 |
| Z_j | n_j d | unspecified |

The n_j are positive integers and sum_j n_j^2=22. These exhaust the
simple objects: the Z_j are exactly those whose forgetful image has no
invertible summand. The object X is self-dual because it is the unique
simple of its dimension. In particular n_j d cannot equal 1+2d, by
irrationality of d.

Use the normalized modular S matrix of Z(F), with positive vacuum row.
Since sqrt(Dim Z(F))=Dim F=6r, its vacuum row is

    (b, a, 1/3,1/3,1/3, 1/6,1/6,1/6,1/6, n_j sqrt(3)/12),

where

    b=(2-sqrt(3))/12, a=(2+sqrt(3))/12.

Choose a cyclotomic Galois automorphism sigma sending sqrt(3) to
-sqrt(3). Galois symmetry gives a signed permutation of the rows,

    sigma(S_0j)=epsilon_sigma(0) S_hat_sigma(0),j.

At j=0 the left side is a>0, so positivity forces epsilon_sigma(0)=+1.
The unique vacuum-row entry equal to a is the one labelled X. Hence
hat_sigma(0)=X and its entire row is forced:

    S_Xj=(a, b, 1/3,1/3,1/3, 1/6,1/6,1/6,1/6, -n_j sqrt(3)/12).

No choice of twists or unknown entries of S enters this conclusion.
Since X is self-dual, the Verlinde coefficient is

    N_XX^X = sum_j S_Xj^3/S_0j
           = a^3/b+b^3/a + 3/9 + 4/36 - 22/48
           = 97/72 + 32/72 - 33/72
           = 4/3.

This is impossible for a fusion coefficient. Thus p=q=1 does not occur
in any pseudounitary categorification of Z3+6. Necessarily {p,q}={0,2};
in particular its center contains the nondegenerate pointed Z3 factor
extracted by the standard induction argument. Identifying the remaining
rank-nine factor's full modular data remains a separate task.

For a transparent check of the only nontrivial arithmetic, a+b=1/3 and
ab=1/144. Therefore a^2+b^2=7/72 and

    a^3/b+b^3/a=((a^2+b^2)^2-2a^2b^2)/(ab)=97/72.

Primary inputs:

* [Larson, Pseudo-unitary non-self-dual fusion categories of rank 4,
  Section 4](https://arxiv.org/pdf/1401.1879), for the induction table.
* [Dong--Lin--Ng, Congruence property in conformal field theory,
  Theorem II(iii)](https://msp.org/ant/2015/9-9/ant-v9-n9-p03-s.pdf),
  for the normalized signed Galois-row identity. The Verlinde formula is
  used for a self-dual object, so this step also does not assume C* unitarity.
