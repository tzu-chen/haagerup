# Final skeptical audit of the conditional identification

23 September 2026, structure-routes agent. This is a source and logical
dependency audit, not a rerun of the exact certificates. No numerical job
was launched. It audits `hi_cft_20260923_next_conditional_identification.md`
and the linked rationality, branching, rank-four, rank-six and character
notes as they stood at approximately 09:45 UTC.

## Verdict and remaining boundary

I found no remaining mathematical gap in the following conditional chain:

1. The actual generated VOA U is strongly rational.
2. If U is proper in B, the sharp top bound and exact finite-top actions
   force the stated B and E8 branching and the rank-four/rank-six fork.
3. The rank-four branches and the rank-six multiplicities m>=2 are
   excluded without assuming that all U modules are unitarizable.
4. The remaining spherical, untwisted Haagerup ring forces the recorded
   modular data and the unique gamma=0 character vector.
5. The stronger ribbon-category identification additionally uses the
   explicitly cited external exhaustive pivotal classification.

Properness remains unproved by these arguments. The positive finite-mode
checks and finite-prime ranks do not select the proper branch. A complete
strong-generation certificate, an exact extra-direction witness, or a
different global argument is still needed. The computer-assisted pivotal
classification is an external theorem dependency, not a computation
independently replayed in this workspace. These two qualifications have
different roles and must remain separate in the final report.

## Rationality has no remaining rigidity assumption

The positive conformal-vector identity uses regular affine, Potts and
parafermion subalgebras already present before any coset identification.
Thus this argument does not assume the rationality of a coset that is
later deduced from rationality of U.

In the vacuum-projectivity argument, a lowest U space lies in the Zhu
top space for each regular subalgebra: its intrinsic weight agrees with
the ambient weight on that subalgebra, and all operators lowering that
weight annihilate a lowest U vector. Regularity gives a direct sum of
ordinary simple subalgebra modules. Their Zhu-top spaces are precisely
their lowest spaces. This uses no Hermitian form on the arbitrary U
module being considered.

On the finite generalized U-weight-zero space, each partial stress
zero-mode is diagonalizable with nonnegative real spectrum. Taking the
trace of the positive stress identity forces every such operator to be
zero. Simultaneous diagonalization is unnecessary. Only the vacuum
subalgebra modules have zero lowest weight, so the corresponding
translation operators also annihilate the lift. Summing them gives the
vacuum-like vector required to split the epimorphism onto U.

Projectivity of the tensor unit alone was not silently treated as
rationality. The additional rigidity step is supplied by
[Etingof--Penneys, Theorem 1.1](https://arxiv.org/html/2412.17681v3).
The finite abelian braided category of grading-restricted generalized
modules has finite Hom spaces, split idempotents and simple unit. For
each nonzero indecomposable X, the nonzero Grothendieck--Verdier
evaluation onto the unit splits because that unit is projective. Hence
X is non-negligible in the theorem's precise sense.

Moderate growth is not an extra VOA conjecture: realize the finite
abelian category as modules over a finite-dimensional algebra. For fixed
X, right exactness of tensoring gives a constant C_X with
dim(Z tensor X)<=C_X dim Z, by presenting Z as a quotient of finitely
many copies of the regular module. Consequently End(X^n) has at most
exponential dimension, eventually smaller than n!. The theorem gives
rigidity. Tensoring then preserves projectives, and the projective unit
makes every object projective. Semisimplicity follows.

The original McRae modular-character rigidity condition is therefore
not an unverified assumption of the final rationality proof.

## Pseudo-unitarity and the rank reduction

The strict positivity of nonvacuum lowest weights, obtained from the
same regular-subalgebra stress argument, gives positive categorical
dimensions through the usual character asymptotics after strong
rationality has been established. Thus Rep(U) has its positive spherical
structure. This is sufficient for the algebraic argument; a VOA/net
tensor-equivalence theorem is not being substituted for it.

For the Lagrangian algebra H=V(E8), put F=Rep(U)_H. The center equivalence
gives Z(F)=Rep(U). Pseudo-unitarity of F follows from the identities

    dim Z(F) = dim(F)^2,
    FPdim Z(F) = FPdim(F)^2,

and positivity of global dimension over C. The resulting positive
spherical structure is the one in
[ENO, Proposition 8.23](https://annals.math.princeton.edu/wp-content/uploads/annals-v162-n2-p01.pdf).
No C*-structure on F is required.

The h<=17/10 bound concerns every simple U module, not only ambient
unitary sectors. Finite current-Lie-algebra representations are
semisimple algebraically. The exact 80- and 81-dimensional top actions
then justify the all-weight branching because no later top weight is
allowed in those integer-graded sectors. Cyclicity by itself would not
have sufficed; the finite-top certificates also include the required
adjoint and Cartan-eigenline argument.

Adjunction gives rank(F)=dim End_U(H). This uses Y*=Y or Y*!=Y as the two
possibilities, rather than assuming either in advance. Hence the rank
is six or four respectively.

## An entirely spherical replacement for the automorphism citation

The earlier rank note quotes Aut(I(1))=Inv(F) through a paper whose wider
setting is unitary. The full equality is standard, but its surjectivity
is unnecessary here. The following direct argument supplies exactly the
needed statement using the spherical result of
[Bischoff--Jones, Lemma 3.1 and Corollary 3.4](https://arxiv.org/html/1909.02816).

Normalize the canonical connected special Frobenius algebra A=I(1) so
that multiplication followed by comultiplication is the identity.
Write f*g=m(f tensor g)Delta. If f is an algebra automorphism, then

    f*f = f,
    f^(-1)*f^(-1) = f^(-1).

The cited two-product description identifies End(A), with composition
and convolution, with the complex fusion algebra, with fusion product
and [X]*[Y]=delta_XY [X]/d_X. In particular, its minimal convolution
idempotents are d_X[X]. Since d_X>0, f and f^(-1) correspond to sums of
distinct positive terms d_X[X]. Their fusion product is [1]. Positivity
of fusion coefficients forces both supports to consist of one simple
object, and these two objects must be inverse invertibles. Composition
therefore gives a group injection

    Aut_alg(I(1)) -> Inv(F).

The actual order-three lattice automorphisms of H fixing B inject into
Aut_alg(H), so Inv(F) contains Z3. At rank four it must have exactly
three elements. At rank six it has three or six. If it had six, F would
be pointed and Dim(F)=6=3s. Thus s=2 and d(X)=s-1=1. The actual algebra
B=1+X would then be a Z2 simple-current extension, whose sign
automorphism fixes U, contradicting the established pointwise
Aut(B/U)=1. Therefore Inv(F)=Z3 also at rank six.

This proves the invertible-object claim without using the converse
automorphism correspondence, unitarity, or the later Haagerup
classification. It can replace that citation in the dependency chain.

The untwisted associator on this Z3 is a separate conclusion: the local
category of the actual B algebra is the known hyperbolic pointed
Z3 x Z3 category. The H algebra in it gives a full tensor embedding of
its module category into F. A nontrivial Vec(Z3)^omega would have the
wrong center metric group/twists. Thus the pointed subcategory used in
the indicator formulas is genuinely untwisted; the order-three group
of objects alone would not have established this.

## Rank-four and rank-six exclusions

The finite rank-four multiplicity list is the published
[Dong--Chen--Wang Theorem 6.2](https://doi.org/10.1016/j.jalgebra.2022.02.020),
not the weaker older preprint statement. It is not restricted to
C*-categorifications. The multiplicity-zero sign argument and the
multiplicity-two electric A4 extension argument both apply to the
algebraic positive spherical setting. The latter uses the VOA
commutative-algebra extension correspondence and holomorphic central
charge-eight classification; it does not presume that the newly
constructed holomorphic extension has a separately supplied unitary
structure.

For multiplicities three and six, the final universal induction,
indicator and modular-data arguments replace the earlier comparison
with only the familiar affine models. In particular, the balanced
m=6 branch is ruled out by signed Galois symmetry and a nonintegral
Verlinde coefficient. The remaining character arguments use stable
weighted projections, so they do not require unproved independence of
characters or an assumed complete branching of all B modules.

For rank six, the noncommutative fusion algebra and three invertibles
force the recorded quadratic ring. The induction multiplicities,
first two indicator moments, and weighted root count were independently
checked. The exceptional equality case in the root-sum lemma explicitly
requires its second moment to lie in Q(sqrt(10)); the indicator equation
does supply that hypothesis. Galois averaging is not being claimed to
preserve an arbitrary second moment. This was the substantive earlier
gap in that lemma, and the final version repairs it.

Thus the exclusion of m>=2 has no surviving assumption of subfactor
realizability, complete unitarity, or an exhaustive generalized
near-group classification.

## Modular data, characters, and the stronger ribbon conclusion

The surviving spherical untwisted m=1 ring meets the hypotheses of the
Gannon--Schopieray--Yadav modular-data theorem cited in the dedicated
scope audit. That conclusion is modular data, not by itself a braided
equivalence. The character uniqueness argument additionally uses the
actual c=8 exponent/pole bounds and dim U1=6; a matching finite list of
low coefficients alone is not its justification.

The upgrade to the ribbon center of H3 invokes the exhaustive pivotal
classification stated in [Vercleyen's thesis, Section 4.4 and Table 9.1](https://mural.maynoothuniversity.ie/id/eprint/18958/1/phd.pdf).
Its scope is pivotal multiplicity-free categories, which includes this
positive spherical ring. The thesis reports four Haagerup-Izumi Z3
classes. The explicitly constructed four classes of
[Evans--Gannon, Theorem 3](https://arxiv.org/html/1506.03546)
then account for that upper bound. Their construction alone is not
being used as an exhaustion theorem.

The two negative-dimensional classes cannot be repivotalized to become
positive: the fusion ring has trivial tensor automorphism group of the
identity, since rho^2 contains both 1 and rho and then all the other
simples. The two positive classes are the known Morita-equivalent
Haagerup categories. Center equivalence plus uniqueness of the positive
spherical structure gives the ribbon conclusion.

The thesis's exhaustive equation-solving records were not independently
replayed here. A report claiming an entirely self-contained tensor
classification would therefore be too strong. The conditional modular
data and full character conclusion do not need this last exhaustion
step.

## Statements this audit does not establish

- U is proper in B.
- A finite-prime normal-span rank is an upper bound in characteristic
  zero, or a tested subset of OPEs closes the whole generated VOA.
- The three selected weight-four vectors are minimal strong generators;
  selected normal-word independence does not prove an upper bound for
  every unselected normal word.
- Complete unitarity of every U module, or full VOA/net tensor and
  braiding compatibility. Operator-algebra and physical applications
  that use those bridges must retain their separate hypotheses.
- Identification of the physical c approximately 2 chain with a c=2
  tensor factor of the chiral c=8 VOA. The separate c=6 coset statements
  do not provide such a factorization.

Within these boundaries the conditional identification is logically
coherent. The unresolved construction step is properness, not a hidden
rank-four or rank-six C*-categorification assumption.
