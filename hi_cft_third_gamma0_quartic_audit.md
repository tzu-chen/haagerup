# Fourth current moments after the finite ground filters

This is a finite-only necessary test for the actual Haagerup-center modular
representation and Evans–Gannon gamma0 c8 character. It is not a claim about
the physical chain or the existence of a VOA. The new standalone source is
`hi_cft_third_gamma0_quartic_check.py`; ROOT owns all execution.

## Jacobi normalization and the complete weight-four space

For commuting orthogonal Cartans put

\[
Q_u=\operatorname{Tr}(u_0^2q^{L_0-c/24})/\kappa_u,
\quad R_{uv}=\operatorname{Tr}(u_0^2v_0^2q^{L_0-c/24})/(\kappa_u\kappa_v).
\]

The two-variable Gaussian Jacobi transformation in
[Krauel–Mason](https://arxiv.org/abs/1103.0994) gives the weight-four forms

\[
H_{uv}=R_{uv}-{E_2\over12}(Q_u+Q_v)+{E_2^2\over144}\chi,
\qquad
H_{uu}=R_{uu}-{E_2\over2}Q_u+{E_2^2\over48}\chi.
\]

Only the vacuum pole is present. Since the vacuum coefficient of
`D_2 D_0 chi` is1/6, particular solutions are `D_2 D_0 chi/24` and
`D_2 D_0 chi/8`. This avoids assuming that the raw fourth trace is itself
modular. The complete holomorphic M4 space is the independently audited
three-dimensional eigenspace of `B_omega` with eigenvalue1152, represented
by `(Delta/E4^2) Xi v`.

Its leading vectors satisfy

\[
\mathcal L(v)=v_0-27v_{c1}-13v_{d1}-13v_{d4}=0.
\]

Direct exact coefficients give
`L(D2Dchi)=3/2` and `L(E2^2 chi)=−279`, including all vacuum-pole
cross terms. Consequently

\[
\mathcal L(R_{uv})=2+{\mathcal L(Q_u)+\mathcal L(Q_v)\over12},
\qquad
\mathcal L(R_{uu})=6+{\mathcal L(Q_u)\over2}.
\]

CFT independently checked the Jacobi normalization and vacuum pole.
ROOT independently derived the same-axis relation. Neither calculation
uses nonnegative coset energy on a nonvacuum module.

## Exact finite representations and two independent polynomial checks

For an SU2 irrep of dimension n the ordinary moments are

\[
I_n={n(n^2-1)\over6},\qquad
S_n={n(n^2-1)(3n^2-7)\over60}.
\]

These are `Tr h^2/2` and `Tr h^4/4`. A tensor irrep `(n,m)` contributes
`m I_n,n I_m,I_n I_m,m S_n,n S_m`. The literal finite-weight sums are
independent selftests. Fourth moments may be half-integral; the source
never silently rounds them. Symmetric representation forms make them
integral, because each quaternionic type has even multiplicity.

Let `a=t_c1`, `c=t_d4` on each factor and `r_j` denote the mixed ground
moment. For levels `(k,l)` the exact mixed polynomial is

\[
40kl-28(k+l)-45(ka_R+la_L)-13(kc_R+lc_L)
-162r_{c1}-78r_{d1}-78r_{d4}=0.
\]

On either factor the same-axis polynomial is

\[
40k^2-56k+16-90ka-26kc
-54s_{c1}-26s_{d1}-26s_{d4}=0.
\]

The source does not rely only on these simplified expressions: it fits
the three M4 coefficients to the three known grounds, predicts the
vacuum coefficient, and independently verifies equality to each
polynomial residual. The vacuum moments are mixed0 and same-axis8.

ROOT executed the fully reviewed certificate at21:41:38UTC, including
the dimension13/14 joint quartic support search. Exactly `(1,39)` and
`(3,13)` survive, one small-ground witness each, in
`hi_cft_third_gamma0_quartic_results.json`. Their minimum current-coset
central charge is18/5. This is a necessary-list result, not existence.

The predicted b ground moments independently agree with CFT's actual
ambient branching calculations: mixed210 and pure(10,22186) for(1,39),
mixed162 and pure(154,1594) for(3,13). Thus the b ground comparison adds
no exclusion. ROOT, CFT and Uniform independently passed the source,
normalizations and resource envelope before execution.

## Additional support tests and honest quantifiers

Once the vacuum identities pass, all twelve leading fourth/mixed
moments are fixed. The source checks nonnegative moments, mixed
integrality, doubled same-axis integrality, and `R_mixed<=t_L*t_R`.
When the inherited symmetric-form filter is present, it also applies
the proven symmetric form to every module except b: each has an odd
published grade (d2 uses777, d6 uses441). This makes the same-axis
moments integral. The b form is not assumed.

The previous d5/d6 output supplies only one quadratic-index support
witness. It must not be treated as the unique decomposition. The new
optional DP instead searches all dimension13/14 decompositions at the
required two indices, mixed moment, and both same-axis fourth moments.
Fixed irrep order with ascending dimension implements unbounded coins;
all five target coordinates are nonnegative and may safely prune.
Quaternionic types enter in pairs only under the inherited parity
premise. The original optional affine-energy filter is preserved and
explicitly labeled; this test adds no new module-energy assumption.

One resulting decomposition certifies support only. DP exhaustion
certifies refusal in the reviewed domain; reaching the resource cap
raises an error and yields no exclusion result.

## Rank-three independent arithmetic

The charge-support proof is in
`hi_cft_third_rank3_quartic_obstruction.md`. Independently checked scalar
consequences are included as controls: at level1 a d4 charge direction
gives `Q_d1=16/13`, `R_d4=72/169`, `R_d1=32/169`, contradicting
`7 R_d1 >= Q_d1^2` by32/169. At level2 the same-axis polynomial equals
−144 for the required d1 triplet. These are finite real-weight facts;
the source controls arithmetic, not the separate charge-rank proof.

## Resource and provenance audit

Pure stdlib only; no NumPy, tensors, eigensolvers, or thread workers.
The input is at most2MiB, with at most400 pairs and1000 saved witnesses.
Each support DP has at most20000 states across15 dimensions and stores
five small integer coordinates plus at most14 irrep labels. DP arrays
are released before the next module/witness. Conservative Python-object
and JSON liveness stays below100MiB; use128MiB AS and a60second alarm.
Immutable input bytes and every transitive producer hash are checked
before computation and again before output promotion. The source refuses
to overwrite a result. All execution was performed by ROOT; no author
numerical job has been launched.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_quartic_check.py --input hi_cft_third_gamma0_d56_orthogonal_results.json --output hi_cft_third_gamma0_quartic_results.json
```

`--identities-only` omits only the larger-ground support DP; it still
checks all three polynomial relations and all leading moment signs and
quantization. An energy-filtered input can be passed separately to retain
that explicitly stronger premise.
