# Exact highest-space certificates for the grade-five gate

23 September 2026. Algebraic design only; no numerical job was launched.
This supplements the finite H=4 strong-generation theorem and the
already source-bound canonical P4 triplet. It does not assert that any
new projected target has passed.

Let W5 be the normal-word space generated in weight five from K, S2,
S3 and the canonical P4 triplet. The passed current controls imply that
W5 is stable under the two current sl2 zero-mode actions. The finite
ambient B5 is a semisimple representation of this current Lie algebra.

Write E,F,H for standard sl2 generators, with [E,F]=H. On the weight-w
line of V_j, where j is the nonnegative integral highest weight,

    FE = (j-w)(j+w+2)/4.

Here FE means first apply E_0 and then F_0. For w>=0 define

    P_w(FE) = product over j=w+2,w+4,...,Jmax
              (1 - 4 FE / ((j-w)(j+w+2))).

The upper endpoint is adjusted to the parity of w. This polynomial is
the projector from the weight-w space onto its highest-weight vectors
of highest weight w. It kills every larger highest-weight summand and
is the identity on the desired summands. No Hermitian-form computation
or eigenvector normalization is required.

For B5 the Cartan vectors have squared norms 2 and 78. A lattice state
has momentum squared norm at most 10, so Cauchy--Schwarz gives absolute
Cartan weights at most floor(sqrt(20))=4 and floor(sqrt(780))=27.
Every highest weight occurs as an actual Cartan weight, so the uniform
bounds Jmax,L=4 and Jmax,R=27 are valid. At a split prime all displayed
denominators must be explicitly checked nonzero before projection.

Apply the commuting projector

    P_(l,r) = P_l(F_L E_L) P_r(F_R E_R)

to raw normal-word columns in Cartan weight (l,r). Their projections
remain in W5 because W5 is current-stable. Each projection has a fully
replayable recipe involving only rational coefficients and current
zero modes applied to the original normal word. Thus selecting columns
by linear algebra modulo a split prime does not compromise a later
exact positive-membership certificate.

## Targets and why the three channels suffice

Let a be a highest S2 field of current highest weight (mL,mR). Let p+
be the highest canonical P4 field of type (0,2), with p0=F_R p+ and
p-=F_R^2 p+. For k=0,...,min(mR,2), set

    t_k = P_(mL,mR+2-2k) (a_0 F_R^k p+).

The charged-field highestness is an existing exact input, rather than
an inference from the projected targets: `hi_cft_20260923_c8_exact_check.py`
explicitly checks both raising zero modes on all eight charged fields.
The source-bound output is
`hi_cft_20260923_c8_exact_unitary_certificate.json`. Their Cartan weights
are read directly from their homogeneous lattice supports. Independently,
the exact minimal lowering-string nilpotence in `x.descendants` forces
the same highestness in a finite semisimple sl2 representation.

The two neutral fields e,f are K singlets as follows. Their sum is the
K-coset stress T=omega-Sug(K), whose mode1 kills K. Their exact PCT and
Virasoro controls, together with the passed ambient quasiprimary checks,
make e1 and f1 positive semidefinite on the ambient current space: positive
Virasoro modes annihilate a current, and the unitary norm of L(-1)c is
2 times its L(0) expectation. Thus (e1+f1)c=0 forces e1c=f1c=0 for c in K.
The same norm identity gives e0c=f0c=0. Their mode2 actions on a current
vanish by ambient quasiprimaryness, so skew symmetry gives c0e=c0f=0.
This supplies the neutral highestness/trivial-type premise without a new
numerical check.

The first field is therefore p+, p0 or p- with no extra normalization.
Each t_k is a highest vector in the corresponding output type
(mL,mR+2-2k). The left projector acts trivially on an exactly highest
target, but applying it explicitly is a useful consistency control.

The map a tensor p -> a_0 p modulo W5 is K-equivariant. The tensor
product V_mR tensor V_2 is multiplicity-free. The tensor
a tensor F_R^k p+ has nonzero projection onto its k-th summand, while
its other components belong to earlier summands. Equivalently, this
follows from the nonzero extreme coefficient of the Clebsch--Gordan
highest vector. Hence the t_k test one nonzero highest vector in each
summand. Their containment in W5 forces the whole A-family by P4
tensor-product map to vanish modulo W5.

Thus all three projected tests are required for mR>=2, two for mR=1,
and one for mR=0. For the eight charged highest S2 families there are
23 such tests. One of the two neutral families supplies one more. The
other neutral zero-mode is recovered from omega minus the two current
Sugawara stresses, as in the separately audited neutral-field lemma.
This gives 24 independent projected channels for the grade-five gate.

## Safe finite-prime discovery and exact replay

A prime projected-span computation may discover candidate relations
and a small independent subset of projected normal columns. The final
certificate must replay those recipes in the exact field and verify
each complete sparse target minus its column combination is zero.
A prime zero residual alone is not an exact containment.

It is sufficient to use any subset of actual projected normal words
that contains the target exactly. The procedure does not need a
characteristic-zero upper bound for the full normal span. Conversely,
a nonzero residual against an incomplete selected span does not prove
that the target is outside W5 or outside U.

If complete K-stable normal spaces and their weight dimensions are
already known, their highest multiplicities satisfy

    mult(l,r) = dim W5(l,r) - dim W5(l+2,r)
                - dim W5(l,r+2) + dim W5(l+2,r+2).

This is an efficiency estimate, not a substitute for the positive
exact relations. A partial list of raw columns need not have these
dimensions or be closed under the currents before projection.

The projectors can reduce the exact solve from a whole Cartan block
to its current-highest multiplicity space. They do not enlarge the
authorized resource caps and do not justify an unbounded solve.
