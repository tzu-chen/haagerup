# Host497 is excluded by simultaneous current traces

15 September2026. Exact algebra, independently reviewed by ROOT and
CFT_constraints. The first weight-two certificate was executed by ROOT;
the tiny joint-representation certificate below is prepared for its slot.

Let W be a strongly regular unitary c8 VOA whose actual modular
representation is that of the Haagerup center and whose character is
the gamma1 vector, beginning1+19q+198q²+1307q³ after q^(−1/3).
Then W cannot contain commuting A3_1 and A1_5 current factors. In
particular the surviving host497 current algebra is excluded under
these premises. The argument does not require rationality of its
commutant or an E8 fixed-algebra/hypergroup restriction theorem.
It does not by itself identify the lattice-chain continuum CFT.

## 1. The universal exact trace relation

The primary Jacobi identity and rational modular reduction are proved
in [the current-trace audit](hi_cft_third_flavoured_trace_audit.md).
They use [Krauel–Mason, Theorem1](https://arxiv.org/pdf/1103.0994),
and the full fundamental matrix of
[Evans–Gannon, equations(1.24),(2.7)](https://arxiv.org/pdf/1006.1326).
No scalar holomorphic c24 formula is used.

ROOT executed `hi_cft_third_flavoured_trace_check.py` at20:38UTC.
The exact result is [the saved certificate](hi_cft_third_flavoured_trace_results.json).
Its holomorphic M2 basis, in the ordered coordinates
0,b,a,c0,c1,c2,d1,d2,d3,d4,d5,d6, is

    (3/2,3/2,−3/2,−3/2,−1/6,1,0,0,0,0,0,0),
    (1,−1,0,0,0,0,−2/5,2/5,−9/5,−1/5,1,0),
    (0,0,0,0,0,0,−3/5,−7/5,9/5,1/5,0,1).

Every basis vector v therefore satisfies

    v_0+9v_c1−v_d5=0.

The explicitly constructed particular quadratic current trace has
coefficients129/28,1/4,6/7 in these positions, and

    129/28+9(1/4)−6/7=6.

For EVERY current u this proves

    Tr_(W1)(u0²)/kappa
      +9 Tr_(c1 ground)(u0²)/kappa
      −Tr_(d5 ground)(u0²)/kappa =6.                 (1)

The three terms refer respectively to vacuum grade1 and module
grounds(c1: dimension3,h1/3; d5: dimension8,h7/13). They are not
traces at one common conformal weight. Relation(1) follows from the
vector modular representation, which couples their different
fractional exponents. The c1,d5 labels are EG's published ordering.

## 2. What the A3_1 trace forces on the eight-dimensional ground

As proved in the preceding audit, A3 acts trivially on the c1,d1,d4
grounds. The d1 assertion can be derived from the second universal
trace identity with constant8 and the adjoint index8, without any
affine-versus-total module energy bound. Those conditions fix its weight-two
trace. The executed solution gives

    Tr_(W1)(u0²)/kappa=8,
    Tr_(d5 ground)(u0²)/kappa=2.

The first agrees with the A3_1 adjoint trace: A3 alone survives the
test. The second is additional information about a nonvacuum module.

Every full W-module ground is killed by positive affine-current
modes, so its A3 constituents are integrable affine highest-weight
ground representations. At level1 they are1,4,6,4bar, with ordinary
quadratic indices0,1,2,1 and dimensions1,4,6,4. The full module is
selfcontragredient; consequently4 and4bar occur equally often.
Dimension8 together with trace index2 leaves exactly

    4+4bar,       or       6+1+1.                    (2)

Each nontrivial A3 type in(2) has multiplicity one. A commuting A1
must act trivially on each such multiplicity space, by Schur's lemma.
It can act nontrivially only on the two A3 singlets in the second case.
Thus its ordinary SU2 quadratic trace index on this ground is

    t_d in {0,1}.                                  (3)

This permits the doublet and imposes no Frobenius–Schur sign condition.

## 3. The incompatible A1_5 trace

On a three-dimensional vector space, any finite SU2 representation
is1+1+1,2+1,or3. Their ordinary indices, normalized to index1 for a
doublet, are

    t_c in {0,1,4}.                                (4)

For an affine A1_k current, kappa is k times the normalized Lie
form. Its adjoint has ordinary index4, so(1) becomes

    4+9t_c−t_d=6k.

At k=5 this requires

    9t_c−t_d=26.

But(3),(4) give only0,−1,9,8,36,35. No pair works. This excludes the
simultaneous A3_1/A1_5 factors. An additional central U1 does not
change the conclusion: it commutes with both and contributes zero
to their adjoint traces.

More generally, without any A3 assumption, positivity t_d>=0 in(1)
already gives6k<=40 for any simple A1_k factor of a gamma1 W.
Therefore every such level satisfies k<=6. This additional bound is
specific to gamma1; it has not been applied to the gamma0 host33.

## 4. Bounded independent certificate and provenance

`hi_cft_third_flavoured_joint_check.py` reads only the saved exact
trace JSON (cap128KiB), verifies its original producer SHA against
the unchanged source, checks the functional on every vector of the
complete M2 basis and its particular constant6, then enumerates the
two A3 representations and the finite SU2 options. All arithmetic is
integer/Fraction. It saves every option, the empty feasible set and
the explicit theorem scope. No numerical approximation or q-series
truncation enters the certificate.

There are fewer than ten candidate representation options and only
a small input JSON. Total process estimate64MiB, first guard128MiB
AS,10second alarm. The author performed only an AST parse.

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_flavoured_host497_obstruction.md --audit-json hi_cft_third_flavoured_joint_guard.json -- python hi_cft_third_flavoured_joint_check.py --output hi_cft_third_flavoured_joint_results.json

ROOT independently checked the normalization and simultaneous
representation argument. CFT_constraints independently checked the
Jacobi factor, elliptic modular space, low coefficients, A3 ground
restrictions and the FS-free SU2 contradiction. Source audit of the
small joint certificate is requested before ROOT executes it.
