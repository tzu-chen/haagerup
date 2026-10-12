# Finite-closure audit and replacement proofs

27 September 2026. This note is an algebraic and source-code audit. No
numerical job, certificate regeneration, or ambient lattice calculation was
run. The manuscript and frozen certificates were not changed by this audit.

## Findings available for immediate incorporation

1. The recursive strong-generation criterion is valid as stated (with
   `h >= 2`, or the obvious convention when no weight-two generators occur).
   The filtered Wick step admits the complete proof below. It does not need
   linear independence or freeness of normal words, nor a character bound.
2. Gate 5 uses positive `S2`-on-`S3` products inside its normal-product
   identities. The manuscript derives these only in the later properness
   section. This is an exposition/dependency-order defect, not a new missing
   numerical gate: move the Gate-4 bootstrap below between Gates 4 and 5.
   It also proves `K1 P4` and the Virasoro controls on `N5` before Gate 5.
3. The joint-singlet recovery lemma is stronger than its projector-specific
   presentation: any polynomial in current operators that is the identity
   modulo `W4` gives the same conclusion. Its proof does not require an
   ambient dimension computation, and semisimplicity is not needed for the
   actual recovery implication.
4. The phrase "independent verifier" needs a limited scope. The final
   Gate-4 verifier independently replays twelve saved projected vector
   identities with denominator-cleared integer arithmetic. It does not
   independently reconstruct those vectors from their VOA word recipes.
   Old seeds and raising coordinates are source authenticated. This is
   already acknowledged in F1, and should remain explicit after expansion.

## A complete filtered-Wick lemma

Let `V` be a nonnegatively integer-graded vertex algebra with
`V0 = C 1`, and let `S` be a graded subspace of strictly positive weights.
Write `N` for the span of `1` and all expressions obtained from elements
of `S` by translation and arbitrary parenthesized `(-1)` products.
Homogeneous normal expressions have their ambient conformal weight.

**Lemma.** Fix an integer `w`. Suppose `s_n t` belongs to `N` for every
homogeneous `s,t` in `S` with `wt(s)+wt(t)<w` and every `n>=0`.

* All singular products of normal expressions whose total weight is less
  than `w` belong to `N`.
* The same holds at total weight `w` if at least one expression is a
  derivative of a positive-weight expression or is a normal product of
  two positive-weight expressions.

**Proof.** Induct on total weight. The vacuum contributes no singular
products. Sesquilinearity removes a derivative and lowers the total input
weight by one; its resulting powers of the formal variable and translations
preserve coefficientwise membership in `N`. Skew symmetry allows us to put
a composite expression on the right. If it is `:yz:`, use

\[
[x_\lambda:yz:]
=:[x_\lambda y]z:+:y[x_\lambda z]:
 +\int_0^\lambda [[x_\lambda y]_\mu z]\,d\mu.
\]

Both first brackets have smaller total input weight because the omitted
factor has positive weight. Express their coefficients as homogeneous
normal expressions in `N`. A coefficient `x_j y`, `j>=0`, has weight
`wt(x)+wt(y)-j-1`. Its pairing with `z` therefore has total weight at
most `wt(x)+wt(y)+wt(z)-1`, and the induction applies again, unless
it is scalar, when the bracket is zero. The first two terms belong to
`N` because `N` is closed under normal multiplication by definition.
This proves both assertions, including when both original arguments are
composite. No reduction to a preferred normal ordering is being assumed.

The identity is the noncommutative Wick formula in De Sole--Kac,
*Freely generated vertex algebras and non-linear Lie conformal algebras*,
Section 2, <https://arxiv.org/abs/math-ph/0312042>. The reduction above is
an argument inside an existing vertex algebra, not an application of a
nonlinear presentation theorem.

## A complete proof of the recursive criterion

Use the notation in Theorem 3.1 of the original manuscript:
`K=S1`, `A=S2`, and `N` is generated normally and differentially by
`S1,...,Sh`. Assume singular `K`- and `A`-products with every generator
are in `N`, and, for `d>=3`,

\[
S_d\subset A_0S_{d-1}+\mathcal N_d(S_1+\cdots+S_{d-1}).
\]

For `a in A`, the derivation identity
`a0(x_-1 y)=(a0 x)_-1 y+x_-1(a0 y)` and `[a0,T]=0` show immediately
that `a0 N` is contained in `N`. Only its known products with the
generators enter this step.

Induct lexicographically on `(d+e,d)` to prove `s_n t in N` for
`s in Sd`, `t in Se`, and `n>=0`. Left weights one and two are assumed.
For larger `d`, apply the recursive inclusion and linearity. A normal
remainder in lower-weight generators cannot contain a single
undifferentiated generator of weight `d`. It is a derivative or a
composite, so the filtered-Wick lemma handles it using only smaller
total pair weights.

For a remaining summand `s=a0 b`, `b in S_(d-1)`, use

\[
(a_0b)_nt=a_0(b_nt)-b_n(a_0t).
\]

The first term is in `N` by smaller total weight and `a0`-stability.
By the initial hypothesis, `a0 t` has a homogeneous normal expression
of weight `e+1`. Every derivative or composite term in it is handled
by the filtered-Wick lemma: its total weight paired with `b` is `d+e`,
but the composite/derivative reduction uses only smaller total weights.
The only other term is a single generator `r in S_(e+1)`. Its pair with
`b` has the same total weight `d+e` and smaller left weight `d-1`,
so it too is an earlier induction case. If `e=h`, that last possibility
does not occur. All generator singular products consequently close.
The same filtered-Wick induction, now without an upper cutoff, proves
all singular products in `N` close. Normal multiplication and
translation close by construction, and

\[
x_{-r}y=\frac1{(r-1)!}(T^{r-1}x)_{-1}y\qquad(r\ge1)
\]

handles every negative mode. Thus `N` is a vertex subalgebra.

## The bootstrap that should precede Gate 5

Write `A=S2`. The input certificates give `K0 A <= A`, `K1 A <= K`,
`L1 A <= K`, and all primitive-highest `A0 A <= S3`, `A1 A <= A`.
The ten primitive fields (eight charged, two neutral) are quasiprimary.
The affine normal and derivative part is handled by current iterate
identities. Virasoro commutators therefore also give `A2 A <= K`;
`A3 A` is scalar by the ambient grading. In particular, all singular
`A`-on-`A` products are available before Gate 4. Exact provenance gives

\[
S_3=N_3+A_0A,\qquad N_3=K_{-1}A+TA.
\]

These formulas and the current/Virasoro commutators imply

\[
K_0S_3\subset S_3,\quad K_1S_3\subset A,\quad K_2S_3\subset K,
\qquad L(1)S_3\subset A,\quad L(2)S_3\subset K.
\]

For example,

\[
k_1(a_0b)=(k_0a)_1b+(k_1a)_0b+a_0(k_1b),
\]

and, for any weight-two `a`,

\[
[L(1),a_n]=(2-n)a_{n+1}+(L(1)a)_n,
\]
\[
[L(2),a_n]=(3-n)a_{n+2}
 +3(L(1)a)_{n+1}+(L(2)a)_n.
\]

The last term in the second formula is zero for `n>=0`, because
`L(2)a` is scalar. These identities cover non-quasiprimary affine
normal fields as well. They also show

\[
L(1)N_4\subset S_3,\qquad L(2)N_4\subset A,
\]

where `N4=K_-1 S3+T S3+A_-1 A`. Together with the six direct `P4`
Virasoro controls, this proves the same assertions for `W4=N4+P4`
*before* using Gate 4.

Now use Gate 4, `A0 S3 <= W4`. For quasiprimary `a in A` and
arbitrary `p in S3`,

\[
\begin{aligned}
2a_1p&=L(1)(a_0p)-a_0L(1)p\in S_3,\\
a_2p&=L(1)(a_1p)-a_1L(1)p\in A,\\
2a_3p&=L(2)(a_1p)-a_1L(2)p\in K.
\end{aligned}
\]

The next mode is scalar. Current descendants stay quasiprimary because
current zero modes commute with `L(1)`. Current iterate formulas treat
the affine normal summands of `A`. Therefore the conclusion applies to
all of `A`:

\[
A_nS_3\subset
\begin{cases}W_4&n=0,\\S_3&n=1,\\A&n=2,\\K&n=3,\\
\mathbb C\mathbf1&n=4,\\0&n\ge5.\end{cases}
\tag{B1}
\]

The exact construction places `P4` in `A0 S3+N4`; hence the displayed
current commutator, (B1), and `K1 N4 <= S3` give `K1 P4 <= S3`.
No Gate-5 input occurs here. Since currents are primary of weight one,

\[
[L(1),k_1]=-k_2,\qquad [L(2),k_1]=-k_3,
\]

and the already known Virasoro controls on `P4` give `K2 P4 <= A`
and `K3 P4 <= K`. The next mode is scalar. Current-zero stability was
already directly certified. The result extends over all `W4`.

Finally, on the three defining summands of
`N5=K_-1 W4+T W4+A_-1 S3`, the same commutators imply

\[
L(1)N_5\subset W_4,\qquad L(2)N_5\subset S_3.
\tag{B2}
\]

For the only less immediate summand, use

\[
\begin{aligned}
L(1)(a_{-1}p)
 &=3a_0p+(L(1)a)_{-1}p+a_{-1}L(1)p,\\
L(2)(a_{-1}p)
 &=4a_1p+3(L(1)a)_0p+(L(2)a)_{-1}p+a_{-1}L(2)p.
\end{aligned}
\]

Every term has the claimed membership by (B1) and the previously
listed controls. Thus (B1), the positive-current controls, and (B2)
can all be established immediately after Gate 4.

This ordering validates both normal lemmas used by Gate 5. Specifically,
the iterate for `(k_-1 a)_0 p` has inner vectors in
`W4,S3,A,K,C1` and `S3,A,K,C1`; all these memberships now appear
earlier in the text. Gate 5 then gives the stated positive `A`-on-`P4`
products using (B2). The final properness section needs only that last
Virasoro ladder and the recursive criterion.

## Exact scope of the final Gate-4 verifier

The actual final script is
`hi_cft_20260923_c8two_gate4_singlet_verify.py`, not the earlier
`hi_cft_20260923_c8two_gate4_verify.py` alone. It:

* authenticates the 2,145 old seed records and their source graphs;
* authenticates 118 new direct identities and the twelve singlet premises;
* independently recomputes all twelve projected sparse-vector residuals
  by the integer engine in `next_integer_residual.py`;
* checks all 644 saved raising coordinate images and the nine augmented
  rank-322 witnesses at the good split prime;
* combines these with the human-readable raising/singlet lemmas.

The sparse projected target and normal vectors are read from saved vector
records in the exact SQLite file. They are not regenerated by a second
VOA implementation in this final replay. The historical producer and
its source hashes remain part of the trusted computational boundary.
The corresponding Gate-5 verifier is `c8two_jacobi_check.py`. It performs
exact coordinate combinations of the lower relations, authenticates the
two bottom witnesses and both prerequisites, and invokes the documented
algebraic implication. Its Boolean "all24" field is not twenty-four
new ambient grade-five mode calculations.

## Explicit-field provenance: one omitted input repaired

The original `c8two_proof_bundle.json` authenticates 640 files but does
**not** bind either `c8_minimal_generators.json` or its producer. This
omission matters to the exact definition of `U`: the grade-four checkpoint
initializer imports the saved highest fields directly. The minimal
generator producer is the separate calculation that proves all of those
fields, including the neutral stress, belong to the algebra generated by
the six currents, `omega`, and the three-term `u`.

Source inspection of `c8_minimal_generators.py` finds the required argument.
It starts with affine weight-two normal/translation descendants, `omega`,
and `u`, then closes under the four raising/lowering current zero modes
and `u1`. Thus every appended exact vector lies in the actual `U`.
At termination the exact span has dimension 120. It then tests all saved
highest fields and the saved stress against that span, and verifies that
the saved `(2,14)` field equals the displayed three-term `u`. This is a
direct finite generation certificate, not just an identification of
an isomorphic abstract algebra. The root agent reported a successful
fresh exact replay on 27 September (about 1.64 seconds, 34 MiB RSS).

The separate exact `c8_grade3_exact_v2.json` dimension certificate was
also absent from the combined ledger. The exact grade-three checkpoint
already supplies the finite space used in the gate proofs, so this is
not a second mathematical gap; authenticating the independent record
strengthens the displayed 956/634 dimension provenance.

A fresh script, `c8_revision_20260927/authenticate_inputs.py`, supplements
both inputs without modifying any frozen file. It validates their exact
terminal flags, rechecks all source hashes with capped streaming reads,
and can bind fresh root-run replay outputs. Its scope excludes rerunning
the VOA computations and proving any mathematical or analytic lemma.
In particular, the repaired ledger must not be described as a formal
VOA verification.

## Lattice convention check

The exact engine and PCT checker agree with the displayed cocycle and the
three coefficients of `u`. The current triples are

\[
\begin{aligned}
H_L&=a_0(-1)\mathbf1,&E_L&=e^{a_0},&F_L&=-e^{-a_0},\\
H_R&=\sum_i c_i\alpha_i(-1)\mathbf1,&
E_R&=\sum_{c_i\ne0}e^{\alpha_i},&
F_R&=-\sum_i c_i e^{-\alpha_i}.
\end{aligned}
\]

Here the negative coefficients are required by
`epsilon(alpha_i,-alpha_i)=-1`. The vector `a0` pairs trivially with
all simple roots of the selected `A5` and the external `A2`, so the
two affine current factors commute. The two Cartan squared norms are
2 and 78, giving levels 1 and 39. On every selected simple root,
`(sum c_i alpha_i,alpha_j)=2`, giving the Chevalley relation with the
displayed raising current.

If `d=(5,8,9,8,5,1,2,2)`, the transported antilinear PCT is

\[
\theta\bigl(h_1(-n_1)\cdots h_r(-n_r)e^a\bigr)
=(-1)^r\Bigl(\prod_i d_i^{a_i}\Bigr)
  h_1(-n_1)\cdots h_r(-n_r)e^{-a}
\]

for real simple-root oscillators, with coefficient conjugation
`sqrt(-3) -> -sqrt(-3)`, `sqrt(13) -> sqrt(13)`. The source checker
uses exactly this formula. It follows by conjugating the standard PCT
with the torus automorphism `e^a -> prod d_i^(-a_i/2)e^a`. The positive
Hermitian form must be transported at the same time. Its vacuum lattice
vectors have squared norm `prod d_i^(a_i)`, so positivity persists.
The formal current generators need not be individually fixed by PCT;
their spans are stable. The PCT certificate checks both neutral stresses
are fixed and every charged highest field maps into the 120-dimensional
space. Current covariance then gives stability of the full finite space.

The cocycle is bimultiplicative and satisfies
`epsilon(a,b)/epsilon(b,a)=(-1)^((a,b))` and
`epsilon(a,-a)=(-1)^((a,a)/2)`, so it is a valid even-lattice cocycle
with the specified Chevalley signs. No additional finite gate was found
in the source audit.

## Additional immediate consequences of finite closure

Once the normal span is proved equal to `U`, weight bookkeeping gives
`U2=S2` and `U3=S3`, not only `U1=K`: all lower-generator normal words
of weights two and three lie in `S2` and `N3`, respectively. Consequently
the values `dim U2=120` and `dim U3=956` become unconditional consequences
of the finite closure inputs. In degree four one gets `U4=W4`; this
argument does not by itself give `dim U4=6010` because the complete
characteristic-zero dimension of `N4` has not been used or proved here.

## Lean scope and compilation

`lean/HaagerupIzumi/CFT/FiniteClosure.lean` formalizes:

* `nilpotent_raising_saturation`: stable `C` plus
  `M=E M+F M+C` and joint nilpotence imply `C=M`;
* `projected_residual_recovery`: `v-Pv in C` and `Pv in C` imply `v in C`;
* `jacobi_bottom_witness`: the quotient Jacobi equality, a zero witness,
  and a nonzero scalar multiple of the bottom vector force its image zero.

The proof of saturation is descending induction on the length of a word
in two linear operators. It does not assume commutation or finite
dimension separately: joint nilpotence is its explicit hypothesis.
Bounded Cartan weights justify that premise in the manuscript. The
root's first Lean run elaborated the saturation and projection proofs;
it identified a missing `Field` import before the Jacobi lemma, which
has been added as `Mathlib.Algebra.Field.Basic`. Root controls the
subsequent check with

```sh
python lean/safe_lean.py lean/HaagerupIzumi/CFT/FiniteClosure.lean
```

The final root-controlled check passed with exit zero, sampled peak
group RSS 1.541 GiB, and its complete output is
`c8_revision_20260927/lean_finite_closure_final.log`. The source includes
`#print axioms` for all three main lemmas. Their reported dependencies
are respectively `[propext, Quot.sound]`, no axioms, and
`[propext, Classical.choice, Quot.sound]`. Thus these three abstract
components are checked in Lean. This neither formalizes VOA identities
nor converts the saved finite calculations to Lean proofs.

The corrected revision authentication also passed under the default
launcher with the narrower 1024 MiB address cap: it authenticated 650
source/output files in 1.47 seconds, with sampled group RSS 0.022 GiB.
The result is `c8_revision_20260927/finite_input_ledger.json` and the
successful log is `c8_revision_20260927/finite_input_ledger_v2.log`.
The initial refusal log is retained; it arose from the launcher's
relative path spelling, which the revised guard now canonically resolves
against its parent's `/proc` working directory. The guard was not removed.

## Further proof-transport repair

The parafermion first-row reconstruction has a separate complete audit
in `hi_cft_c8_revision_20260927_pf13_reconstruction.md`, with a ready
TeX proposition in `c8_revision_20260927/pf13_reconstruction_snippet.tex`.
It gives a finite acyclic order for reconstructing all `b,b`, `b,d`,
and `d,d` singular products and replaces the implicit universal-VOA
step by a diagonal generated subalgebra of the product of the two
simple algebras. It keeps all exact field/polynomial inputs explicit.
