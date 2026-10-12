# An exact flavoured-character test for the surviving A3_1 current factor

15 September2026. Reading, algebra and source preparation only by this agent.
ROOT owns execution. This note concerns a strongly regular unitary c8 VOA W
with the Haagerup-center modular data and the gamma1 character. It does not
assume a holomorphic c24 current-trace formula.

## 1. The exact Jacobi trace identity

For a Cartan current u put kappa=u_1u and

    chi_j=Tr_(M_j) q^(L0−1/3),
    Q_(u,j)=Tr_(M_j) u_0² q^(L0−1/3).

Choose an integral multiple of a cocharacter so that u_0 has integral
eigenvalues on every irreducible module. Scaling cancels in Q/kappa.
[Krauel–Mason, Theorem1](https://arxiv.org/pdf/1103.0994), PDFp2,
gives the vector Jacobi transformation with exponential
exp(pi i kappa c z²/(c tau+d)). Two z derivatives imply

    F_u=Q_u−(kappa/12) E2 chi in M_2^!(rho).           (1)

Here rho(S)=S_Hg and rho(T)=exp(−2pi i/3) T_Hg. In particular
Q_u/kappa_u−Q_v/kappa_v is modular of weight two.

The sign and factor1/12 follow directly: the anomalous transformation
of Q is kappa c(c tau+d)/(2pi i) times rho chi, while that of E2/12
is c(c tau+d)/(2pi i). The invariant current bilinear form used here
is the coefficient of u_1u, independently of its alternate VOA vacuum
normalization conventions.

The only negative powers of the gamma1 character are the vacuum
q^(−1/3) and a one-dimensional module ground at q^(−7/39), h=2/13.
All Haagerup-center modules are selfcontragredient (S²=1). A
one-dimensional ground is trivial for the semisimple current algebra;
selfcontragredience also negates and hence kills its abelian charge.
Thus every Q_u has no polar term. Differences in(1) are holomorphic.

For a simple affine factor g_k,

    Tr_(W1) u_0²/kappa = 2 hdual/k.                    (2)

The A3_1, A1_5 and central U1 factors of host497 therefore give
8,4/5,0 respectively. These unequal values are allowed in principle:
the relevant vector-valued M_2 space does not vanish.

## 2. The weight-two space has dimension three

Use [Evans–Gannon, equation(2.7)](https://arxiv.org/pdf/1006.1326),
PDFp21, in their ordered basis

    0,b,a,c0,c1,c2,d1,d2,d3,d4,d5,d6.

The fractional T exponents are

    Lambda=(2/3,2/3,2/3,2/3,0,1/3,
            5/39,20/39,32/39,2/39,8/39,11/39),
    Tr Lambda=5.

Direct Gauss-period evaluation of the published S gives Tr S=0 and
Tr(S T_Hg)=3. Thus S has six eigenvalues of each sign, and S T_Hg
has eigenvalue multiplicities(6,3,3) for(1,omega,omega²). The
dimension formula of
[Freitag, Theorem6.1](https://www.mathi.uni-heidelberg.de/~freitag/preprints/riemann-roch.pdf),
which explicitly includes weight2, gives

    dim M2(rho)=12+2−3−3−5=3.                         (3)

The two scalar summands of rho (each with T=omega²) have M2 dimension
zero. Their projections recover the usual E8 extension trace sums;
they do not force the individual simple factors to share hdual/k.

## 3. Replace modular-function evaluation by rational residue equations

The published characteristic matrix chi and Lambda determine a
fundamental matrix

    Xi=q^Lambda(q^(−1)I+chi+...),
    every weak weight-zero vector = Xi P(J),
    J=j−744.

The differential equation underlying EG(1.24) is

    (E10/Delta) D Xi=Xi B(J),   D=q d/dq,
    B(J)=(J−240)(Lambda−I)+chi+[Lambda,chi].            (4)

For H in M2(rho), G=(E10/Delta)H is weakly holomorphic of weight0.
Since Lambda is in[0,1), its cusp pole bound forces G=Xi v with a
constant twelve-vector v. Also

    D J=−E4²E6/Delta,
    dXi/dJ=−Xi B(J)/((J−984)(J+744)).                 (5)

Set Bi=B(984), Bw=B(−744). Their residue eigenvalues are respectively
0,1/2 for −Bi/1728 and 0,1/3,2/3 for Bw/1728. The source verifies the
equivalent exact matrix polynomial identities. There are no logarithms:
the distinct exponents have noninteger differences, and the residues
are diagonalizable. Local ramification J−984 proportional(tau−i)²
and J+744 proportional(tau−omega)³ gives Xi vanishing orders0/1 and
0/1/2. The prefactor Delta/E10 has a simple pole at either elliptic
point. Therefore H=(Delta/E10)Xi v is holomorphic exactly when

    (Bi+864 I)v=0,
    (Bw−576 I)(Bw−1152 I)v=0.                        (6)

These are rational equations in twelve variables. Their common kernel
must have dimension3, independently checking(3). Right-system
normalization in(5) is essential: the stated conditions concern the
coefficient vector v in the published Xi basis.

At the cusp,

    H=q^Lambda(v+(chi+240I)v q+...).                  (7)

No numerical modular evaluation, q-series truncation or fitted rank
is needed.

## 4. A particular trace fixes both polar terms

Write chi0=Xi e0 for the gamma0 character and delta_chi=Xi e8 for
the difference gamma1−gamma0. These statements follow directly from
the published two character vectors and their principal parts.
Derivatives of weight-zero modular vectors have weight two. Hence

    Q_u/kappa = Qpart + H,
    Qpart=E2 chi_gamma1/12 + D chi0/4
                              + (13/28)D delta_chi. (8)

The derivative coefficients are fixed by the polar exponents:
(1/4)(−1/3)=−1/12 and(13/28)(−7/39)=−1/12.
Thus Qpart has no negative powers and any actual normalized current
trace differs from it by exactly the holomorphic space(6).

Its leading nonpolar coefficients in the four relevant components are

| component | exponent | Qpart coefficient |
|---|---:|---:|
|vacuum|2/3|129/28|
|c1|0|1/4|
|d1|5/39|121/182|
|d4|2/39|29/182|

The check source derives these from chi columns0 and8 instead of only
entering the results. It includes the −24q term of E2 acting on each
polar component. This is a common source of an incorrect vacuum trace.

## 5. The A3_1 ground-space obstruction test

The gamma1 ground dimensions and weights force A3 to act trivially on
the c1,d1,d4 lowest spaces:

* c1 has dimension3 and d4 dimension2, below the smallest nontrivial
  A3 representation dimension4.
* The final finite-representation derivation avoids a complementary
  module energy assumption. The complete M2 basis also obeys
  v0+9vc1+vd1+3vd4=0, with particular constant8. For an A3_1 factor,
  its vacuum trace8 and c1,d4 neutrality therefore force d1 trace0.
  Equivalently, for arbitrary A3_k the selfdual6D finite ground has
  index0 or2, so8+t_d1=8k forces k=1 and t_d1=0. A lone4 or4bar
  cannot occur because its conjugate partner would require dimension8.

This replaces the initial heuristic using h_d1<1/2 to forbid the6;
the final theorem does not assume unitarizability of every coset module.
The h=2/13 ground is already used to remove the second pole and is
not a fourth independent holomorphic constraint.

Consequently the exact test is(6) together with

    v_c1=−1/4,  v_d1=−121/182, v_d4=−29/182,          (9)

and, for the required A3_1 adjoint trace8,

    v_0=8−129/28=95/28.                              (10)

This is a potentially overdetermined test, not yet a claimed exclusion
in this source-preparation version. The helper saves the neutral
system's exact rank, particular solution and full nullspace, its
forced vacuum trace when unique, and the augmented A3 consistency.
If the system is inconsistent, the conclusion is conditional on the
strongly regular unitary VOA and actual modular/character premises;
it does not directly exclude an arbitrary nonrational continuum CFT.

## 6. Source/allocation review and ROOT command

New helper: `hi_cft_third_flavoured_trace_check.py`. Only Python's
standard library is imported. Three12×12 products, rational RREFs
with at most28 rows and13 entries per row, a few saved bases and
small JSON dominate. A conservative64MiB total process estimate is
well below the requested128MiB AS guard. A30second alarm and immutable
source SHA/recheck bound the call. No tensor/checkpoint is read and
no common numerical dependency is edited.

The source has exact internal controls for both elliptic residue
polynomials, dimension3, exponent sum5, the four independently
calculated coefficients, and substitution of each consistent RREF
particular/nullspace solution into the original equations. It has
not been executed by its author.

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_flavoured_trace_audit.md --audit-json hi_cft_third_flavoured_trace_guard.json -- python hi_cft_third_flavoured_trace_check.py --output hi_cft_third_flavoured_trace_results.json

CFT_constraints independently checked the complete source and proof:
the published Lambda/chi transcription, elliptic residue signs and
sufficiency, all four particular coefficients, A3 ground neutrality,
the adjoint trace8, and exact RREF/substitution controls all passed.
The author performed only an AST parse. ROOT executed the certificate
at20:38UTC: both exact systems passed, and the neutral conditions fix
the vacuum trace to exactly8. A3_1 therefore survives this test alone.
The resulting d5 trace2 enables the stronger simultaneous A1_5
[obstruction](hi_cft_third_flavoured_host497_obstruction.md).
