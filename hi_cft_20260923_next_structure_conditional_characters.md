# The proper branch has a unique full character vector

This note is conditional on U being proper and on the newly audited
categorical reduction to the standard Haagerup S,T data. Properness is
not inferred from character agreement. The other established inputs are
strong rationality, c=8, a unique lowest-weight-zero simple module, and
dim U1=6.

## The only possible extra pole

The categorical twists have exponents

    0,0,0,0, 1/3,2/3, 2/13,5/13,6/13,7/13,8/13,11/13.

Every character exponent is h-1/3. Strict positivity of nonvacuum h
implies that the only possible negative exponent outside the vacuum
character is -7/39, in the unique twist-2/13 coordinate. Denote its
coefficient by gamma. It is either zero, or the positive integral top
dimension of a module beginning at h=2/13. Every other character is
holomorphic at infinity. The vacuum pole is q^(-1/3) with coefficient1.

Two modular character vectors with the same gamma have the same entire
principal part. Their difference is holomorphic at all cusps, because
the representation has finite image and modular covariance transports
the infinity statement to every cusp. Each component is therefore a
holomorphic function on a compact finite-cover modular curve and is
constant. Such a vector would have to be invariant under S and T.
There is only one T-fixed coordinate, namely the twist-1/3 object; its
S image has a nonzero vacuum component. Hence no nonzero invariant
constant exists. Equal principal parts imply equal character vectors.

This proves an all-weight uniqueness statement, rather than an inference
from finitely many matching coefficients. It also proves that equality
or dependence of some irreducible characters creates no additional
freedom.

## Fixing the single parameter

Evans--Gannon give a fundamental matrix Xi for this representation in
Section2.4, equation(2.7), with the expansion convention from Section1.4.
Its vacuum and d3 columns have exactly the two allowed poles above.
Thus the full character vector is

    ch(U-modules)=Xi[:,0]+gamma Xi[:,d3].

The vacuum current coefficient is 6+13 gamma. Consequently dim U1=6
forces gamma=0, and the complete vector is exactly Xi[:,0]. This is
stronger than needing the separate positivity restriction gamma in{0,1}.
The fundamental matrix is specified to all orders by their recursion
(1.24); it is not merely a finite coefficient fit.

The resulting vacuum expansion begins

    ch U=q^(-1/3)(1+6q+120q^2+956q^3+6010q^4+...).

In particular, properness now implies dim U4=6010 analytically. This
does not imply that a partly computed grade-four generated span already
has dimension6010; it supplies its exact upper target under properness.

The complete list of lowest weights and top dimensions at gamma=0 is:

| Evans--Gannon label | Lowest weight | Top dimension |
|---|---:|---:|
| 0 | 0 | 1 |
| b | 1 | 80 |
| a | 1 | 81 |
| c0 | 1 | 81 |
| c1 | 1/3 | 3 |
| c2 | 2/3 | 27 |
| d1 | 6/13 | 7 |
| d2 | 11/13 | 42 |
| d3 | 15/13 | 119 |
| d4 | 5/13 | 5 |
| d5 | 7/13 | 13 |
| d6 | 8/13 | 14 |

Thus all simple lowest weights in the proper branch are at most15/13,
sharpening the preliminary universal bound17/10. In particular no new
U summand of the three- or27-dimensional lattice sectors can start at
their next integer grade. Coupled with their initial-top irreducibility,
this gives simplicity of those restrictions to all weights.

Primary character source: [Evans--Gannon, The exoticness and realisability
of twisted Haagerup--Izumi modular data, Sections1.4 and2.4,
equations(1.24),(2.7)](https://arxiv.org/pdf/1006.1326).
The newer [Albert--Honda--Kaidi--Zheng paper, equation(12)](https://arxiv.org/html/2512.08225v1)
repeats the vacuum and extension-sector coefficients. The pole uniqueness
argument above isolates the exact role of that supplied fundamental matrix.

## What remains unavailable from this vector alone

The unflavoured character fixes every homogeneous dimension of U and
of its simple modules in this proper branch. It does not by itself
determine the14 separate branching functions for the actual rational
core AL inside U: those require characters with Cartan fugacities,
branching calculations, or another independence argument. In particular
it does not yet determine the full residual character beyond the
independently certified beginning

    ch C_U=q^(-3/20)(1+2q^2+2q^3+O(q^4)).

Neither all-weight character uniqueness nor the explicit Xi vector
constructs the missing noninvertible projection or proves U proper.
