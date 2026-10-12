# The order-three fixed algebra of the F4 coset fits the residual data

23 September 2026. A more precise candidate for Com(A_L,B) is

\[
 C_{std}=\operatorname{Com}(A_{1,13},
             A_{2,1}\otimes A_{2,2}\otimes A_{1,1}),
\]

with the diagonal A1 at levels 4+8+1, using the principal A1 in each
A2. Its central charge is 18/5, its weight-one space vanishes, and
its weight-two space has **dimension five**, matching the exact
ambient calculation. This is a candidate, not an identification.

## Relation to the F4 calculation

The conformal inclusion A2,1 tensor A2,2 in F4,1 has an order-three
simple-current extension: the two nontrivial summands have respective
finite-dimensional tops (3,6bar) and (3bar,6), each of dimension 18
and conformal weight one. Thus its grading automorphism fixes exactly
A2,1 tensor A2,2. It also fixes the embedded diagonal A1,12 and the
external A1,1. Taking the commutant of A1,13 therefore gives

\[
 C_{std}=Y^{\mathbb Z_3},\qquad
 Y=\operatorname{Com}(A_{1,13},F_{4,1}\otimes A_{1,1}).
\]

The preceding note's dimension-thirteen calculation excludes Y as
Com(A_L,B). It does not exclude Y as Com(A_L,V_E8), whose weight-two
space was not part of that calculation. A Z3 extension between these
two opposite commutants is compatible with B⊂V_E8 of index three.

## Exact dimension-five count

The nineteen ambient currents restrict under the diagonal sl2 as
3V_2+2V_4. Count horizontal singlets at grade two factor by factor.
For A2,1, Sym^2(8)=1+8+27 has two principal-sl2 singlets, and its
level-one null representation 27 removes one, leaving one. For
A2,2 there is no integrability null at grade two, leaving two.
The external A1,1 contributes its one Sugawara singlet. The three
cross-factor terms contribute 2,1,1 respectively. Their sum is eight.

The diagonal affine vacuum contributes one singlet at grade two.
The two complementary V_2 current tops contribute one descendant
singlet each. There is no weight-one commutant. Hence

\[
 \dim(C_{std})_2=1+2+1+2+1+1-1-2=5.
\]

## A finer test from the c=4/5 axis

Let e be the Potts stress in Com(A1,8,A2,2). Its zero mode has the
following spectrum on this five-dimensional Griess algebra:

\[
 0\text{ with multiplicity }3,\qquad
 \frac25\text{ with multiplicity }1,\qquad
 2\text{ with multiplicity }1.
\]

The zero eigenspace is the weight-two algebra of the triple diagonal
coset Com(A1,13,A1,4 tensor A1,8 tensor A1,1), of central charge 14/5.
The eigenvalue-two line is e itself. The remaining line arises from
pairing the spin-two currents in the two A2 factors. The A2,2
spin-two current has A1,8 conformal weight 3/5, so its Potts weight
is 2/5; the A2,1 current has no Potts weight. This accounts for all
five dimensions.

The unique exact ambient c=4/5 axis found by
`hi_cft_20260923_next_structure_residual_axis.py` can be tested against
this spectrum by the separate ambient verifier. Matching the spectrum
and even the entire Griess multiplication would still need an
all-weight VOA argument before asserting an isomorphism.

## Rationality and category motivation

The standard candidate contains a rational conformal frame with
central charges 4/5, 64/35, 34/35. The first is the Potts coset,
the second is the level-four diagonal A1 coset, and the last is the
unitary minimal Virasoro model M(14,15). Rationality of the level-four
coset is supplied by [Lin](https://arxiv.org/abs/2107.09400).
Thus this is a plausible source of an actual rational residual frame;
finding its stress vectors alone would not identify the higher
generators of the level-four factor.

At the category level the extra pointed factor of size nine relative
to the F4 coset agrees with the nine sectors of B. The natural
expected factors are Fib^rev, SO(3)_13^rev and the hyperbolic pointed
Z3 squared category. This is motivation for comparing the embeddings,
not an independently proved category statement for the actual
residual commutant.

The familiar conformal E6,1 inclusion of G2,1 tensor A2,2 and the
conformal G2,1 inclusion of A1,1 tensor A1,3 place the standard
ambient construction inside B. Its immediately visible mirror has
six currents, whereas the actual A_L has four. Therefore the
existence of that standard construction by itself does not identify
our actual embedding or its mirror.
