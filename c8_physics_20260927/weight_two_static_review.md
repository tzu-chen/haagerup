# Independent static review of the complete weight-two tensor

Reviewer: analytic agent, 2026-09-27. This review read the source and
mathematical construction. It did not execute a generator, verifier,
numerical job, or lattice mode calculation. The reported successful runs
belong to the root agent's guarded execution record.

## Result

The mathematical interpretation of the 113-dimensional primary basis,
the highest-first seed slice, the current-Ward completion, and the
normalized sparse three-point tensor is sound, conditional on the
manuscript's actual lattice realization and established dimensions
dim(U_1)=6 and dim(U_2)=120. No missing positive Virasoro-mode condition,
factorial, projection term, complex conjugation, or phase correction was
found. Two small executable crosslink-coverage improvements were reported
to root and implemented; the updated checker was re-read and its changes
are correct. Stale source comments were also reported. The review did not
edit executable sources or change their hashes.

Reviewed files:

- `full_weight_two.py`
- `complete_weight_two.py`
- `check_physics_crosslinks.py`
- `couplings.tex`
- the relevant helpers in `hi_cft_20260923_c8_exact.py` and
  `c8_reviewability_20260927/check_readable_inputs.py`
- the complete tensor report and the manuscript's weight-two decomposition

## Primarity and completeness

For a homogeneous lattice state v of weight two,
`mode(omega,2,v)` is L(1)v and `mode(omega,3,v)` is L(2)v.
Checking both is sufficient. All L(n)v for n>=3 belong to negative
weight spaces and therefore vanish in this positive-energy lattice VOA.
Alternatively L(1) and L(2) generate the positive Virasoro Lie algebra,
so their joint kernel already consists of highest vectors.

There is no extra test for Cartan-weight-zero components: Cartan weight
and conformal weight are different gradings, and the same Virasoro
conditions are tested on every component, including the three stress
singlets and the zero-Cartan-weight components of nontrivial multiplets.

The affine left factor contributes 4 states at weight two (three current
derivatives and its stress tensor); the affine right factor contributes
9 (three derivatives, its stress, and a spin-two multiplet of dimension5).
Their mixed current products give dimension9, the two coset stresses
give dimension2, and the eight original charged multiplets give
dimension96. The sum is120. The proposed primary complement has
96+5+9+3=113 states.

More intrinsically, the orthogonal complement of the primary space in
U_2 is L(-1)U_1 plus the total stress tensor. The six derivatives are
independent because their squared norms are twice the corresponding
current norms; the stress tensor has positive norm c/2=4 and is
orthogonal to those derivatives. Taking adjoints of L(1) and L(2)
therefore proves the dimension formula120-6-1=113. The code constructs
113 positive-norm primary vectors and checks all potentially nonzero
off-diagonal Gram entries. Distinct Cartan weights are orthogonal
because the Cartan zero modes are self-adjoint in the positive form.
These facts establish completeness, not only independence.

The membership of the original eight highest fields and the two coset
stresses in the short-defined U is an input from the manuscript's
minimal-generation and structural certificates. The export does not
independently reconstruct that membership argument.

## Current multiplets and raw lowering

The engine's `descendants` function actually applies the left and right
lowering zero modes, with no factorial division. It also asserts that
the next right-lowering vector at each left level vanishes, and that
the next left-lowering vector vanishes. The component order is left
power first, right power second, exactly as used in the completion code.

The matrices F v_p=v_(p+1) and E v_p=p(n-p)v_(p-1) are consequently
the correct raw-basis matrices for a dimension-n irreducible sl2 module.
The right and left actions commute. Highest-vector status is supplied
by the established current multiplets; it can also be deduced from
the checked weights and terminal lowering conditions in the finite
unitary sl2 representation. A vector of weight n-1 satisfying F^n v=0
has no component in an irreducible module of larger highest weight.

The five-dimensional added right multiplet is the traceless symmetric
current product. The nine-dimensional mixed multiplet comes from
products of the two commuting current algebras. The level-one left
spin-two product is null. The three displayed stress combinations
are mutually orthogonal for the metric diag(c_i/2), and satisfy
sum_i a_i c_i=0, hence are primary relative to the total stress tensor.
Their actual primary conditions and positive norms are checked as well.

## Projection and Ward completion

All calculations occur in the finite-dimensional space U_2, so no
unbounded-operator domain assertion is involved. Current zero modes
commute with the total Virasoro algebra. The primary space is invariant
under the compact current group and its complexified Lie algebra, and
its orthogonal complement is invariant under their adjoints. Orthogonal
projection P onto the primary space therefore commutes with every
current zero mode.

The mode derivation identity gives exactly

    P((F v_i)_(1) v_j) = F P((v_i)_(1) v_j)
                         - P((v_i)_(1) (F v_j)).

The recursive source order ensures that the entire preceding first-slot
row is already known before this formula is used. Even when the second
slot is lowered, its entry lies in that preceding row. No unknown
same-row value is used. Seed products with no compatible primary charge
can correctly be omitted: their primary projection is zero by Cartan
covariance, independently of their descendant components.

For equal-weight-two states, VOA skew-symmetry says that the difference
between a_(1)b and b_(1)a is a derivative of a weight-one state; the
possible higher derivative of the vacuum vanishes. Primary projection
annihilates this difference. Thus the checked tensor symmetry in its
first two slots is the correct identity.

Every current raising/lowering identity and every first-two-slot
symmetry is checked on the completed tensor. Additional direct lattice
products compare complete primary projections, not only one selected
coefficient. These probes are consistency tests; the logical reason
the completion determines every entry is the exact equivariant
recursion and the complete highest-first seed slice.

## Hermitian normalization and phases

The independent Fock pairing is antilinear in its first slot and uses
the transported positive torus gauge. The algebraic field has basis
(1,s,t,st), with s=sqrt(13)>0 and t=i sqrt(3). `conj(2)` fixes s and
negates t and st, so it is the required complex conjugation. Exact sign
tests on Q(sqrt(13)) are used; the positive norms are not inferred from
floating-point approximations.

Let N_i=<v_i,v_i>. The stored raw projection coefficient is
p_ij^k=<v_k,(v_i)_(1)v_j>/N_k. Completion acts on these raw coefficients.
The export reconstructs the numerator as p_ij^k N_k and divides by
sqrt(N_i N_j N_k), choosing positive square roots. This is precisely
the coefficient of the unit target field in the OPE of the two unit
source fields. The numerator retains its complex phase. The associated
three-point function places the conjugate target at infinity. Since
all three fields here have even weight two, no additional odd-spin
radial-adjoint sign is concealed by this convention.

The omitted sparse entries are zero only in this complete weight-two
Virasoro-primary projection. They do not assert that the unprojected
mode product vanishes: current derivatives and the total stress tensor
can still occur. They also do not specify nonvacuum module
intertwiners or left-right bulk sewing coefficients.

## Independent u-channel check

The highest state v7_0_0 is u, and the normalized lowest state v7_1_13
has the unique primary Cartan weight(-1,-13). It therefore equals the
normalized adjoint of u up to a phase. Summing the squared coefficients
for that pair over every primary target is independent of this phase.
The separate Gaussian four-point calculation gives the global
weight-two coefficient14/3. The total stress contribution is1, so the
primary tensor must give11/3. The three stress-difference targets must
give sum_i(2 h_i^2/c_i)-1. These are valid independent normalization
checks linking the tensor and the explicit four-point functions.

## Reported coverage and documentation repairs

At the time of the initial static read, `check_physics_crosslinks.py`
loaded and hashed `correlators.json` but did not read its actual
four-point coefficients: the numbers14/3 and11/3 were hard-coded.
It also assumed rather than asserted the meanings of basis indices68,
95 and110--112. Root was asked to compare directly with the recorded
neutral global weight-two and projected-primary values, verify the
corresponding basis labels/charges/multiplets, and include the basis
file in the crosslink report's source hashes. The mathematical
equalities themselves were correct. Root implemented all three changes;
the reviewer re-read the updated checker and found the resulting direct
record comparisons and index assertions correct.

At the initial read, the opening docstrings of the two full-tensor scripts contained
96-field/eight-highest descriptions inherited from the earlier slice.
The completion docstring also advertised a 300-second timeout without
installing a corresponding internal alarm. These do not change the
computed tensor; resource enforcement for the recorded runs came from
root's permanent guarded launcher and the script's1GiB address-space
precondition. Source-comment updates should be reflected in the final
hash manifest rather than silently retaining old source hashes.
Root updated the field-count comments and scheduled fresh guarded runs.

The scripts are research certificates, not an independently formalized
lattice VOA or an adversarial input validator. In particular, output
hashes and the final manifest bind the reviewed source and data; the
completion script does not revalidate every upstream engine/source hash
while loading its input reports. All Python `assert` checks require a
normal interpreter run, not optimization mode. No Lean kernel claim is
made for these exports.
