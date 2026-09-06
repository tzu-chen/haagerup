# Haagerup–Izumi \(\mathbb Z_n\): transparent \(F\)-symbols, class fields, and Stark-unit route

## Purpose

This is a research handoff summarizing the current working picture for cyclic Haagerup–Izumi fusion categories in the transparent gauge, with emphasis on:

1. reducing the \(F\)-symbol system to one core matrix \(A\);
2. the exact algebraic reconstruction for the \(\mathbb Z_{17}\) Q-system branch;
3. evidence that the generic \(F\)-symbol field is a ray class field of
   \[
   K_p=\mathbb Q\!\left(\sqrt{p^2+4}\right);
   \]
4. the candidate relation between normalized \(F\)-symbols and Stark units;
5. reproducible PARI/GP tests and the remaining analytic construction problem;
6. exact construction without HI seeds, uniform cocycle/sign reductions,
   and an infinite family of arithmetic inputs over one quadratic field.

Some statements below are exact consequences of the transparent-gauge identities or exact algebraic manipulations. Others are computational conjectures based on reconstruction from published Evans–Gannon numerical seeds and should be independently verified.

> **Further continuation (2026-09-05).** Sections 34–40 prove that the full phase-ansatz Izumi system is equivalent to one balanced finite beta identity, including its collision corrections. They extend sign descent to composite orders and show that its stabilizer obstruction always vanishes at odd prime powers under the stated root/phase hypotheses. Complete exact constructions now also pass at \(n=19,25,199\); the latter belongs to the fixed-\(\mathbb Q(\sqrt5)\) Lucas family. The order-19 polynomial recognition is discharged as well. Saved coefficient data and independent verifiers accompany all three cases. The prime-power construction now uses one Kummer root, twisted norm descent, and a rational linear system for the signs. The quadratic-to-cubic ideal containment is verified at orders 3, 5, 7, and 9. Infinitude remains unproved; Sections 37–40 specify what a uniform proof still requires.

> **Existence continuation (2026-09-04).** Sections 28–33 go beyond field comparisons. A cocycle argument determines every generic fourth power from the labeled doubling orbit. The new `hi_stark_seedless.gp` constructs complete matrices directly from PARI Stark polynomials, with no numerical HI seeds, and verifies every Izumi equation exactly for \(n=7,11,13,17,29\). It also identifies the previously recognized \(n=13\) polynomial and all three \(n=17\) polynomials with the certified matrices. Their numerical-recognition qualifications in the earlier historical sections are therefore removed by this continuation. Infinitude is **not** proved: Section 32 supplies an unconditional infinite family of arithmetic inputs over the fixed field \(\mathbb Q(\sqrt5)\), and Section 33 specifies the uniform identities still needed.

> **Update (2026-09-04).** The PARI tests have now been completed for \(p=7,11,13,17,19\). For \(p=7\), and conditional on the initial numerical recognition for \(p=13,17\), the normalized HI square generates the same ray field as PARI's distinguished Stark unit and is the exact group-ring transform \(s^{2-\operatorname{Frob}_{(2)}}\), rather than the same distinguished generator. At \(p=19\), the ray group is \(C_{18}\times C_2\), and the two published HI branches are the two Hilbert-class conjugate halves of its full degree-36 orbit. See Sections 21–27 and the reproducible GP scripts listed at the end.

---

# 1. Fusion rules and notation

Let
\[
G=\mathbb Z_N,\qquad N\text{ odd},
\]
with invertible simple objects \(\alpha^a\), \(a\in\mathbb Z_N\), and noninvertibles
\[
\rho_a:=\alpha^a\rho.
\]

The fusion rules are
\[
\alpha^a\alpha^b=\alpha^{a+b},
\]
\[
\alpha^a\rho_b=\rho_{a+b},
\qquad
\rho_a\alpha^b=\rho_{a-b},
\]
and
\[
\rho_a\rho_b=\alpha^{a-b}+\sum_{c\in\mathbb Z_N}\rho_c.
\]

The Frobenius–Perron dimension of \(\rho\) is
\[
d=\frac{N+\sqrt{N^2+4}}2,
\qquad
d^2=Nd+1.
\]

For the prime-order discussion below I write \(N=p\).

---

# 2. Transparent gauge: all noninvertible \(F\)-symbols from one matrix

The transparent-gauge structure strongly suggests that all \(F\)-symbols are determined by:

- universal values \(1,d^{-1/2},d^{-1}\) when invertible channels occur;
- one \(N\times N\) core matrix
  \[
  A_{a,b}
  :=
  \left(F^{\rho,\rho,\rho}_{\rho_a}\right)_{\rho,\rho_b}.
  \]

A useful reconstruction formula obtained from the transparent translation identities is

\[
\boxed{
\left(
F^{\rho_{a_1},\rho_{a_2},\rho_{a_3}}_{\rho_{a_4}}
\right)_{\rho_{a_5},\rho_{a_6}}
=
A_{\,
a_4+a_2-a_1-a_3,\,
a_5+a_6-a_1-a_3
}
}
\]
with all indices modulo \(N\).

In particular,
\[
\boxed{
\left(F^{\rho,\rho,\rho}_{\rho_a}\right)_{\rho_e,\rho_f}
=
A_{a,e+f}.
}
\]

Thus for fixed \(a\), the noninvertible block of
\[
F^{\rho,\rho,\rho}_{\rho_a}
\]
is anti-circulant.

This is the main structural reason the enormous pentagon system should reduce to a much smaller algebraic problem.

---

# 3. Identification with the Izumi / Evans–Gannon \(A\)-matrix

For known examples, the transparent \(F\)-core appears to coincide with the Izumi/Evans–Gannon structure matrix \(A_{g,h}\).

The standard symmetries include
\[
A_{g,h}
=
A_{-h,g-h}
=
A_{h-g,-g}.
\]

For a unitary solution,
\[
A_{h,g}=\overline{A_{g,h}}.
\]

The maps
\[
R(g,h)=(h-g,-g),
\qquad
S(g,h)=(h,g)
\]
generate
\[
S_3\simeq W(A_2).
\]

For real solutions, \(A\) is constant on the \(S_3\)-orbits in \(\mathbb Z_N^2\). For complex unitary solutions, reflections can act by complex conjugation.

For \(3\nmid N\), the number of \(S_3\)-orbits in \(\mathbb Z_N^2\) is
\[
\frac{(N+1)(N+2)}6.
\]

---

# 4. Q-system phase parametrization

For the unitary Q-system branch, the generic entries can be written in terms of phases \(j_g\).

Set
\[
z_g=e^{ij_g}.
\]

For generic \(g,h\),
\[
A_{g,h}
=
\frac{\sqrt d}{d-1}
e^{i(j_h-j_g-j_{h-g})}
=
\frac{\sqrt d}{d-1}
\frac{z_h}{z_gz_{h-g}}.
\]

The exceptional values are
\[
A_{0,0}=1-\frac1{d-1},
\]
and
\[
A_{g,0}=A_{0,g}=A_{g,g}
=
-\frac1{d-1}
\qquad (g\neq0).
\]

This phase form should be viewed as a discrete multiplicative second derivative of the one-dimensional sequence \(z_g\).

A major possible route to a uniform construction is to Fourier-transform the Izumi equations in the \(z_g\) variables.

---

# 5. The explicit \(\mathbb Z_{17}\) setup

For \(p=17\),
\[
d=\delta
=
\frac{17+\sqrt{293}}2.
\]

Define
\[
B_{g,h}:=(\delta-1)A_{g,h}.
\]

Then
\[
B_{0,0}=\delta-2,
\]
\[
B_{g,0}=B_{0,g}=B_{g,g}=-1
\qquad(g\neq0),
\]
and for generic entries
\[
|B_{g,h}|=\sqrt{\delta}.
\]

The ratios \(t=h/g\in\mathbb F_{17}\setminus\{0,1\}\) split into three \(S_3\)-orbits:
\[
\mathcal O_2=\{2,9,16\},
\]
\[
\mathcal O_3=\{3,6,8,10,12,15\},
\]
\[
\mathcal O_4=\{4,5,7,11,13,14\}.
\]

Therefore the \(289\) core positions split into only five algebraic types:

- \(A_{0,0}\);
- the common axis/diagonal value;
- generic type \(\mathcal O_2\);
- generic type \(\mathcal O_3\);
- generic type \(\mathcal O_4\).

---

# 6. Exact algebraic reconstruction for \(\mathbb Z_{17}\)

Starting from the published numerical Evans–Gannon phase seed and refining it to high precision, one obtains degree-\(16\) orbit polynomials over
\[
K_{17}=\mathbb Q(\delta)
=
\mathbb Q(\sqrt{293})
\]
for the scaled generic entries \(B\).

For the three ratio classes there are irreducible degree-\(16\) polynomials
\[
P_2,\quad P_3,\quad P_4
\in K_{17}[X].
\]

The corresponding actual \(A\)-entries have minimal polynomials over \(K_{17}\)
\[
Q_t(X)
=
\frac{P_t((\delta-1)X)}{(\delta-1)^{16}}.
\]

After eliminating \(\delta\), the generic \(A\)-entries have irreducible degree-\(32\) polynomials over \(\mathbb Q\).

The special values satisfy:
\[
A_{g,0}=A_{0,g}=A_{g,g}
\quad\Longrightarrow\quad
17X^2-15X-1=0,
\]
and
\[
A_{0,0}
\quad\Longrightarrow\quad
17X^2-49X+31=0.
\]

The exact Sage data from the previous reconstruction is in:

`z17_haagerup_izumi_minpolys.sage`

This includes:

- the three \(P_t\) over \(K_{17}\);
- the three degree-\(32\) rational polynomials;
- irreducibility checks;
- the special transparent values.

---

# 7. Class-field hypothesis

For prime \(p\), define
\[
K_p
=
\mathbb Q(\delta),
\qquad
\delta=\frac{p+\sqrt{p^2+4}}2.
\]

Since
\[
N_{K_p/\mathbb Q}(\delta)=-1,
\]
one has
\[
N(\delta-1)=-p,
\qquad
N(\delta+1)=p.
\]

Define the degree-one prime
\[
\mathfrak p_+=(\delta-1)
\]
above \(p\).

The natural narrow ray modulus suggested by the physical embedding is
\[
\boxed{
\mathfrak m_p=\mathfrak p_+\infty_+,
}
\]
where \(\infty_+\) is the real place with
\[
\delta>0.
\]

If:

1. \(h(K_p)=1\);
2. \(\delta\) is a fundamental unit;

then the ray class group should have order
\[
p-1
\]
and in favorable cases
\[
\operatorname{Cl}_{\mathfrak m_p}(K_p)
\simeq
\mathbb F_p^\times
\simeq
C_{p-1}.
\]

This matches the observed generic entry-field degrees for \(p=7,13,17\).

---

# 8. Computational class-field evidence

## \(p=7,13,17\)

For the principal branch, the reconstructed generic entry field has degree

\[
p-1
\]
over \(K_p\).

A polynomial transformation implementing
\[
u\mapsto gu
\]
for a primitive root \(g\bmod p\) was reconstructed and checked algebraically to permute the roots.

This indicates
\[
\operatorname{Gal}(L_p/K_p)
\simeq
C_{p-1}
\simeq
\mathbb F_p^\times.
\]

A Frobenius / Artin comparison was then performed at many split primes, using the expected ray character arising from
\[
\mathfrak m_p=(\delta-1)\infty_+.
\]

The observed Frobenius permutations matched the predicted ray-class action in all tested cases for \(p=7,13,17\).

The polynomial discriminants also fit the ray-class prediction after dividing by perfect-square index factors.

Expected relative field discriminant:
\[
\boxed{
\mathfrak D_{L_p/K_p}
=
\mathfrak p_+^{p-2}.
}
\]

This is consistent with a conductor-\(\mathfrak p_+\) abelian extension.

### Status

The ray groups, conductors, discriminants, and field identifications have now been reproduced with exact PARI class-field routines for \(p=7,13,17\). The \(p=7\) HI input is exact; the \(p=13,17\) conclusions remain conditional only on their numerical-to-exact HI polynomial reconstructions. Independent Magma replication would still be useful.

---

# 9. The \(p=11\) exception

Here
\[
K_{11}
=
\mathbb Q(\sqrt5).
\]

Let
\[
\epsilon=\frac{1+\sqrt5}{2}.
\]

Then
\[
\delta
=
\frac{11+5\sqrt5}{2}
=
\epsilon^5.
\]

Thus \(\delta\) is **not** the fundamental unit.

This changes the ray-class calculation.

The simple modulus
\[
(\delta-1)\infty_+
\]
has ray class group of order \(2\), not \(10\).

Evans–Gannon have two \(\mathbb Z_{11}\) Q-system branches.

For the second branch, the apparent degree-\(10\) orbit collapses to five copies of one quadratic polynomial over \(K_{11}\):
\[
Q(X)
=
X^2
+
\frac{5+3\sqrt5}{2}X
+
\frac{11+5\sqrt5}{2}.
\]

Its discriminant is
\[
\operatorname{disc}Q
=
-(\delta-1).
\]

This looks exactly like the quadratic ray field of conductor
\[
(\delta-1)\infty_+.
\]

The principal degree-\(10\) \(p=11\) branch is arithmetically different. The continuation in Section 22.2 identifies the conductor of its reconstructed unit field as
\[
(\delta-1)\mathfrak q_5^2\infty_+
=5(\delta-1)\infty_+,
\]
where \(\mathfrak q_5\) is the ramified prime above \(5\).

### Important lesson

The correct global statement is probably **not**
“every generic HI entry field is always the simple \((\delta-1)\infty_+\) ray class field.”

Instead, HI branches seem naturally organized by ray class arithmetic, with unit-index and class-group effects causing exceptional splitting and alternate conductors.

---

# 10. The \(p=19\) class-group phenomenon

For
\[
K_{19}
=
\mathbb Q(\sqrt{365}),
\]
the class group is exactly \(C_2\), and \(19-\delta=-\delta^{-1}\) is a fundamental unit.

The simple ray modulus
\[
(\delta-1)\infty_+
\]
has ray class group
\[
\operatorname{Cl}_{(\delta-1)\infty_+}(K_{19})
\simeq C_{18}\times C_2,
\]
of order \(2(19-1)=36\).

Evans–Gannon give two \(\mathbb Z_{19}\) Q-system branches.

For either branch separately, the 18-element set
\[
\{B_{u,2u}:u\in\mathbb F_{19}^\times\}
\]
does not form a degree-\(18\) polynomial over \(K_{19}\).

However, combining the 18 values from **both branches** gives an irreducible degree-\(36\) polynomial over \(K_{19}\).

Numerical reconstruction followed by exact conductor and Hilbert-class calculations proves, conditional only on recognition of the phase polynomial, that

\[
\boxed{
\text{the two \(p=19\) HI branches are two halves of one ray-class Galois orbit,}
}
\]
with the nontrivial ideal class exchanging the branches. Section 26 gives the exact field data and isolates the remaining numerical recognition step; an independent Magma replication would still be useful.

---

# 11. Stark-unit candidate

This is the most promising new observation.

For \(p=17\), define
\[
U_{g,h}
=
\frac{B_{g,h}}{\sqrt{\delta}}.
\]

For generic entries,
\[
|U_{g,h}|=1
\]
under the physical embedding.

On the \(t=2\) orbit, define
\[
\boxed{
\varepsilon_u
=
-U_{u,2u}^{\,2}
=
-\frac{B_{u,2u}^2}{\delta}.
}
\]

Observed properties of \(\varepsilon_u\):

1. \(\varepsilon_u\) is an algebraic unit.
2. It has degree \(16\) over \(K_{17}\).
3. It generates the same field as \(B_{u,2u}\).
4. Its minimal polynomial over \(K_{17}\) is reciprocal.
5. One has
   \[
   \varepsilon_{-u}=\varepsilon_u^{-1}.
   \]
6. The Galois action is
   \[
   \sigma_a(\varepsilon_u)=\varepsilon_{au}.
   \]
7. Under the conjugate real embedding of \(K_{17}\), all 16 Galois conjugates of \(\varepsilon_1\) are positive real numbers.

These are exactly the qualitative features expected from a rank-one Stark / Shintani unit orbit for the ray extension
\[
K_{17}^{(\delta-1)\infty_+}/K_{17}.
\]

The initial working conjecture was:

\[
\boxed{
-\frac{B_{u,2u}^2}{\delta}
\quad\text{is a Stark unit, or a fixed integral power of a canonical Stark unit.}
}
\]

Equivalently,
\[
\boxed{
U_{u,2u}
=
\pm i\sqrt{\varepsilon_u}.
}
\]

The appearance of the square root is notable because recent SIC-POVM constructions from real quadratic ray class fields also express unit-modulus overlap phases in terms of square roots / powers of Stark units.

The exact comparison in Section 21 refines this statement. The HI unit is not itself a root of PARI's Stark polynomial, nor a pure power orbit of such a root. It does, however, lie in the same ray field and satisfies, after compatible choices of roots and a cyclic Galois generator \(\sigma\),

\[
\boxed{
\varepsilon_{\mathrm{HI}}^2
=
\frac{s^2}{\sigma^2(s)},
}
\]

where \(s\) is a root of PARI's `bnrstarkunit` polynomial. Thus the robust conjecture is the broader one: normalized HI phases are roots of short products or quotients of Stark conjugates.

---

# 12. PARI/GP Stark-unit test

This test was completed with PARI/GP 2.17.4; full results are in Section 21.

For \(p=17\), construct

\[
K=\mathbb Q(\delta),
\qquad
\delta^2-17\delta-1=0.
\]

Then construct the ray class field for
\[
\mathfrak m=(\delta-1)\infty_+.
\]

Schematic GP:

```gp
bnf = bnfinit(y^2 - 17*y - 1, 1);

\\ inspect real embeddings first
polrootsreal(y^2 - 17*y - 1)

\\ prime ideal generated by delta - 1
pp = idealhnf(bnf, y - 1);

\\ PARI orders the roots increasingly, so [0,1] selects delta > 0
bnr = bnrinit(bnf, [pp, [0,1]], 1);

bnr.clgp
S = bnrstarkunit(bnr);
lift(S)
```

Important implementation details:

- `[0,1]` is the infinite-place bit for the positive embedding \(\delta>0\); `[1,0]` gives a ray group of order \(8\), not \(16\);
- construct \(\mathfrak p_+\) from `delta-1`, rather than relying on the ordering returned by `idealprimedec`;
- inspect the ray class group;
- compare the returned Stark polynomial with the exact minimal polynomial of
  \[
  \varepsilon_1=-B_{1,2}^2/\delta.
  \]

Possible outcomes:

### A. Exact polynomial match

Then the normalized HI phase is literally a square root of the canonical Stark unit, up to inversion and a root of unity.

### B. Same field, polynomial related by a power map

Then
\[
\varepsilon_{\mathrm{HI}}
=
\varepsilon_{\mathrm{Stark}}^k
\]
for some integer \(k\), which is still excellent.

### C. Same field but unrelated unit-lattice class

Then class-field theory remains relevant, but the strong Stark-unit hypothesis is false.

### Actual outcome: same field and a short Stark-orbit quotient

The two polynomials are unequal and there is no pure-power orbit relation, but the fields are \(K_{17}\)-isomorphic and an exact two-conjugate relation exists:

\[
\varepsilon_{\mathrm{HI}}^2
=
\frac{s^2}{\sigma^2(s)}.
\]

This is stronger than outcome C and points toward a multiplicative-difference or cocycle formula.

---

# 13. Independent Magma replication

The analogous PARI calculations are now complete for \(p=7,11,13,17,19\). The following remains a useful independent verification plan.

For each \(p=7,13,17,19\):

1. Construct
   \[
   K_p=\mathbb Q(\sqrt{p^2+4}).
   \]

2. Compute:
   - ring of integers;
   - unit group;
   - class group;
   - factorization of \(p\);
   - prime ideal \(\mathfrak p_+=(\delta-1)\).

3. Construct the ray class group for
   \[
   \mathfrak p_+\infty_+.
   \]

4. Construct the corresponding class field.

5. Compare:
   - degree;
   - discriminant;
   - ramification;
   - Galois group;
   - Artin action at small primes.

6. For \(p=17\), reproduce the exact identification of the reconstructed \(B_{1,2}\) field with the class field.

7. Reproduce the test that
   \[
   \varepsilon=-B_{1,2}^2/\delta
   \]
   is not a pure power of one Stark conjugate but satisfies the exact Frobenius quotient relation.

For \(p=19\), independently reproduce the \(C_{18}\times C_2\) ray group, the Hilbert class field \(\mathbb Q(\sqrt5,\sqrt{73})\), and the exact Hilbert-conjugate factorization of the recognized HI polynomial.

For \(p=11\), independently verify the PARI result that the principal degree-\(10\) branch has conductor \(5(\delta-1)\infty_+\).

---

# 14. Higher-priority structural problem: derive all generic entries from one Stark orbit

The exact relation for
\[
\varepsilon_u=-B_{u,2u}^2/\delta
\]
as a Frobenius quotient of Stark conjugates gives only the ratio class \(t=2\).

For \(p=17\), we still have the other two generic orbit types:
\[
t\in\mathcal O_3,
\qquad
t\in\mathcal O_4.
\]

The next task is to ask whether these can be expressed using products or quotients of Stark conjugates.

Try relations of the form
\[
U_{g,h}^{\,2}
\stackrel{?}{=}
-\varepsilon_{a}^{m}
\varepsilon_{b}^{n}
\varepsilon_{c}^{r},
\]
where \(a,b,c\) are simple linear or cross-ratio functions of \(g,h\).

More natural tests:

\[
\frac{U_{1,t}^2}{U_{1,2}^2},
\]
\[
\frac{U_{1,t}U_{1,1-t}}{U_{1,2}},
\]
\[
U_{g,h}U_{h,g},
\]
\[
U_{g,h}U_{-h,g-h}U_{h-g,-g}.
\]

Search for multiplicative relations in the unit group of the ray field using:

- Magma `UnitGroup`;
- PARI `bnfisunit`;
- integer relations among logarithmic embeddings.

If all generic \(U_{g,h}\) can be expressed as products of square roots of one Stark-unit Galois orbit, then the entire transparent associator may admit a direct class-field construction.

---

# 15. Fourier / cocycle route

The phase parametrization
\[
U_{g,h}
=
\frac{z_h}{z_gz_{h-g}}
\]
suggests that \(U\) is a multiplicative second difference.

A major goal is to find \(z_g\) directly in class-field terms.

Possible ansatz:
\[
z_g
=
\frac{Q_p(\zeta_p^g)}
     {Q_p(\zeta_p^{-g})},
\]
or a variant built from:

- Gauss sums;
- Jacobi sums;
- Gaussian periods;
- Stark/Shintani units;
- Shintani–Faddeev cocycle values at real multiplication points.

If \(z_g\) can be produced directly, all \(U_{g,h}\) follow automatically.

Then the Izumi equations should be Fourier transformed. Since they contain cyclic convolution sums, Fourier space may turn them into lower-dimensional multiplicative identities.

---

# 16. Potential Shintani–Faddeev route

The real quadratic number
\[
\delta=\frac{p+\sqrt{p^2+4}}2
\]
is the fixed point of
\[
x\mapsto p+\frac1x,
\]
represented by
\[
\begin{pmatrix}
p&1\\
1&0
\end{pmatrix}.
\]

This makes \(\delta\) a natural real-multiplication point.

The modulus
\[
(\delta-1)
\]
has norm \(p\), suggesting rational characteristics of denominator \(p\).

A first plausible formula was schematically
\[
U_{u,2u}
=
\zeta\,
{}^{\mathbf r_u}[\delta],
\]
where
\[
\mathbf r_u\in \frac1p\mathbb Z^2/\mathbb Z^2
\]
indexes the ray class and the right-hand side is a Shintani–Faddeev / real-multiplication cocycle value.

The exact comparisons show that a single Stark value is too restrictive. The revised target is a quotient of a value and its Frobenius-at-\((2)\) translate, whose square matches
\[
U_{u,2u}^4
=
\frac{s_u^2}{s_{2u}}
\]
up to the fixed signs and normalizations described in Sections 21–27.

This could eventually provide an explicit nonnumerical construction.

---

# 17. Long-term existence strategy

The numerical-to-algebraic reconstruction should be treated as a discovery tool only.

A viable infinite-family proof would ideally look like one of the following.

## Strategy A: direct ray-class / Stark formula

Construct canonical Stark representatives \(s_u\) in
\[
K_p^{(\delta-1)\infty_+}
\]
and define the HI units by the Frobenius quotient
\[
e_u^2=s_u^2/s_{2u},
\]
then define \(F\)-symbols algebraically from suitable roots and products of these units.

Then prove the Izumi equations by class-field or cocycle identities.

## Strategy B: analytic Shintani–Faddeev formula

Define the \(F\)-symbols from explicit special-function values at the RM point \(\delta\).

Prove the Izumi identities analytically.

Since an isolated solution of polynomial equations over a number field has algebraic coordinates, algebraicity could then follow from rigidity rather than from direct Stark algebraicity.

## Strategy C: finite field + Hensel lifting

Define the Izumi solution modulo suitable primes using character sums.

Prove the mod-\(\mathfrak q\) solution is smooth.

Hensel-lift to a \(p\)-adic algebraic solution.

This can prove existence without ever computing complex minimal polynomials.

---

# 18. Concrete next-step checklist

## First priority: verify the Stark comparison at \(p=17\)

- [x] Reconstruct / load exact \(P_2(B)\).
- [x] Compute exact minimal polynomial of
  \[
  \varepsilon=-B^2/\delta.
  \]
- [x] Run `bnrstarkunit` for
  \[
  K_{17},\quad(\delta-1)\infty_+.
  \]
- [x] Compare polynomials exactly: unequal, but the relative fields are exactly \(K_{17}\)-isomorphic.
- [x] Test power relations
  \[
  \varepsilon_{\mathrm{HI}}=\sigma(\varepsilon_{\mathrm{Stark}})^k.
  \]
  No pure-power relation occurs; an exact short orbit relation does.
- [x] Identify the quotient automorphism as arithmetic \(\operatorname{Frob}_{(2)}\) by exact reduction modulo \(2\).

## Second priority: repeat at \(p=7,13\)

- [x] Complete the \(p=7\) comparison from Evans–Gannon's exact algebraic solution.
- [x] Complete the \(p=13\) comparison from its reconstructed numerical branch.
- [x] Formulate the sharpened Stark-orbit quotient conjecture suggested by all three cases.
- [x] Verify the Frobenius-at-\((2)\) identification in both cases.

## Third priority: \(p=19\)

- [x] Identify the degree-\(36\) ray class field and its group \(C_{18}\times C_2\) exactly.
- [x] Verify, after numerical polynomial recognition, that the combined HI orbit defines this full ray field.
- [x] Identify the Hilbert class field and prove that its involution interchanges the exact branch factors.
- [x] Compare with the full Stark orbit: the fields agree exactly, and a separated numerical search finds a branchwise generator-of-\(\langle\operatorname{Frob}_{(2)}\rangle\) quotient law.

## Fourth priority: \(p=11\)

- [x] Confirm the second branch equals the quadratic simple ray field, including its affine normalization to PARI's Stark unit.
- [x] Determine the apparent conductor of the reconstructed principal degree-\(10\) branch.
- [x] Check whether the prime above \(5\) enters the conductor: it enters as \(\mathfrak q_5^2=(5)\).
- [ ] Compare its modular-data distinction with conductor arithmetic.

## Fifth priority: recover all \(A_{g,h}\) from Stark units

- [x] Obtain a uniform fourth-power expression for every generic entry (Section 28), bypassing separate unit-group searches.
- [x] Lift it to complete exact matrices for \(n=7,11,13,17,29\), including all three \(\mathbb Z_{17}\) ratio types (Section 29).
- [x] Determine coherent signs by linear equations over \(\mathbb F_2\), leaving only a global generic sign (Section 30).

## Sixth priority: general symbolic formula

- [x] Give a single phase-sequence formula including exceptional entries (Section 31).
- [x] Fourier transform the entire quadratic system for arbitrary odd \(n\) (Section 31).
- [ ] Prove the Fourier identities and the cubic system for a uniform analytic construction.
- [ ] Search for a class-field / character-sum ansatz.

---

# 19. Main conjectural picture

The current working conjecture is:

\[
\boxed{
\text{Cyclic Haagerup–Izumi Q-system \(F\)-symbols are class-field-theoretic objects over }
K_p=\mathbb Q(\sqrt{p^2+4}).
}
\]

More specifically:

1. the relevant algebraic fields are narrow ray class fields, or closely related sub/extensions, with modulus involving
   \[
   (\delta-1)\infty_+;
   \]

2. the normalized unit-circle generic \(F\)-symbols are roots of short products or quotients of Stark conjugates; for the exact \(p=7\) solution and the reconstructed \(p=13,17\) candidates, the same exact quotient form holds, and reduction at the inert prime \((2)\) identifies the relevant field automorphism as arithmetic Frobenius at \((2)\), up to the global Artin-reciprocity inversion convention;

3. the relabeling symmetry
   \[
   g\mapsto ug
   \]
   is the Artin action of
   \[
   \mathbb F_p^\times;
   \]

4. class-group effects explain multiple HI branches: at \(p=19\), the two reconstructed branches are exactly the Hilbert-class conjugate factors of the full ray-field polynomial once the initial phase recognition is accepted;

5. exceptional unit structure explains anomalies such as \(p=11\);

6. a direct Stark/Shintani construction may provide a route to proving existence for infinitely many cyclic Haagerup–Izumi categories without numerical algebraic reconstruction.

---

# 20. References to keep open

Primary HI / Izumi references used in this exploration:

- [Huang–Lin, arXiv:2007.00670](https://arxiv.org/abs/2007.00670)  
  Transparent gauge and explicit \(F\)-symbol calculations.

- [Evans–Gannon, arXiv:1506.03546](https://arxiv.org/abs/1506.03546)  
  Non-unitary fusion categories and their doubles via endomorphisms; a later generalization of the HI/Q-system framework.

- [Evans–Gannon, arXiv:1006.1326](https://arxiv.org/abs/1006.1326)  
  Twisted Haagerup–Izumi modular data; Section 4.1 contains equations (4.1)–(4.3), the exact \(p=7\) construction, and the numerical phase seeds for \(p=11,13,17,19\).

Stark / real quadratic references to inspect:

- [PARI/GP documentation for `bnrstarkunit`](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html#bnrstarkunit).
- [Kopp, *The Shintani–Faddeev modular cocycle: Stark units from q-Pochhammer ratios*, arXiv:2411.06763](https://arxiv.org/abs/2411.06763).
- [Kopp, *SIC-POVMs and the Stark conjectures*](https://doi.org/10.1093/imrn/rnz153). Its quadratic base field is different from the HI field here, so this is a structural analogy rather than a direct identification.

---

# 21. Completed exact \(p=17\) Stark comparison

All computations in this section were run with PARI/GP 2.17.4 and are reproduced by `z17_stark_test.gp`.

## 21.1 Correct ray modulus

PARI orders the roots of
\[
y^2-17y-1
\]
as
\[
\delta_-=-0.058621\ldots,
\qquad
\delta_+=17.058621\ldots.
\]

Consequently the physical place \(\delta>0\) is the second real place, and the intended input is

```gp
pp  = idealhnf(bnf, delta - 1);
bnr = bnrinit(bnf, [pp, [0,1]], 1);
```

The relevant ray groups are

| infinite part | ray group |
|---|---:|
| none | \(C_8\) |
| \(\infty_-\) | \(C_8\), with redundant infinite part |
| \(\infty_+\) | \(C_{16}\) |
| \(\infty_-\infty_+\) | \(C_{16}\), with redundant \(\infty_-\) |

Thus
\[
\operatorname{Cl}_{(\delta-1)\infty_+}(K_{17})\simeq C_{16}.
\]

## 21.2 Exact HI unit polynomial

Write
\[
P_2(z)=P_e(z^2)+zP_o(z^2)
\]
and let \(e=-B^2/\delta\). Its monic polynomial is obtained exactly as
\[
E(X)
=
\delta^{-16}\operatorname{Res}_z(P_2(z),z^2+\delta X)
=
\delta^{-16}
\left(P_e(-\delta X)^2+\delta X P_o(-\delta X)^2\right).
\]

It has the reciprocal form
\[
E(X)=X^{16}+\sum_{j=1}^7 c_j(X^{16-j}+X^j)+c_8X^8+1,
\]
with
\[
\begin{aligned}
c_1={}&5161\delta-88037,\\
c_2={}&-162681688\delta+2775125324,\\
c_3={}&2224285803398\delta-37943249370668,\\
c_4={}&-13169066631628602\delta+224646121653727220,\\
c_5={}&27687887695366003925\delta-472317193126595318329,\\
c_6={}&-17815979606089964004310\delta+303916050690909978642141,\\
c_7={}&3918293373380552919833799\delta-66840683129156896141024224,\\
c_8={}&-175532701751128886825808423\delta
       +2994345899737840449537231154.
\end{aligned}
\]

Exact checks give:

- \(E\) is irreducible over \(K_{17}\);
- \(E\) is reciprocal with constant term \(1\), so \(e\) is a relative norm-one algebraic unit;
- \(K_{17}(e)=K_{17}(B)\);
- the relative field discriminant is
  \[
  \mathfrak D_{K_{17}(e)/K_{17}}=(\delta-1)^{15};
  \]
- the absolute discriminant is
  \[
  293^{16}17^{15}
  =8445312928482424626719575461796488049229751237996868073393;
  \]
- the absolute signature is \((16,8)\): the physical-place roots lie on the unit circle, while all sixteen roots at the conjugate real place are positive.

## 21.3 Comparison with PARI's Stark orbit

`bnrstarkunit` returns a different irreducible reciprocal polynomial \(S\) of degree \(16\). Nevertheless:

1. \(S\) has the same relative discriminant \((\delta-1)^{15}\).
2. `rnfpolredabs` reduces \(E\) and \(S\) to the same relative field polynomial.
3. Independently, `nfisisom` finds sixteen isomorphisms between their absolute fields, and every one fixes \(K_{17}\).

Therefore the HI unit and PARI's Stark unit generate exactly the same relative ray field.

They are not related by a pure power. An absolute unit-group computation shows that the HI unit vector and every individual Stark-conjugate unit vector have rank \(2\); hence there are no nonzero integers \(a,b\) with
\[
e^a=\pm\sigma(s)^b.
\]

There is, however, a particularly short exact orbit relation. Compatible roots can be chosen so that, for a generator \(\sigma\) of \(G\simeq C_{16}\),
\[
\boxed{
e^2=\frac{s^2}{\sigma^2(s)}.
}
\]

Equivalently, if \(\rho=\sigma^2\) generates the order-eight subgroup \(G^2\), then
\[
e^2=s^2/\rho(s).
\]

This automorphism has an intrinsic ray-class label. The rational prime \(2\) is inert in \(K_{17}\), so
\[
\mathfrak q_2=(2),
\qquad
N\mathfrak q_2=4.
\]
In the common absolute field, exact reduction gives
\[
\rho(s)\equiv s^4\pmod{\mathfrak q_2}.
\]
Consequently \(\rho=\operatorname{Frob}_{\mathfrak q_2}\), not merely an automorphism of the same order. Since the positive generator \(2\) has residue \(2\bmod(\delta-1)\), this is multiplication by \(2\) in the natural ray labeling, with the usual possible inversion depending on the Artin-map convention.

This exact quotient is the strongest evidence so far for a multiplicative-difference or cocycle construction of the HI phases. The algebraic comparison is exact. PARI's interpretation of \(S\) as the characteristic polynomial of an analytic Stark unit remains conditional on the Stark algebraicity conjecture, as documented for `bnrstarkunit`.

---

# 22. Completed \(p=11\) conductor analysis

Let
\[
\delta^2-11\delta-1=0,
\qquad
\epsilon=\frac{\delta-3}{5}=\frac{1+\sqrt5}{2},
\qquad
\delta=\epsilon^5.
\]

## 22.1 Secondary branch: exact quadratic ray field

For \(\mathfrak p_+=(\delta-1)\), the physical modulus \(\mathfrak p_+\infty_+\) has ray group \(C_2\). The polynomial from Section 9 is
\[
Q(t)=t^2+\frac{3\delta-4}{5}t+\delta,
\qquad
\operatorname{disc}Q=1-\delta.
\]

PARI returns the Stark polynomial
\[
S(u)=u^2+\frac{3\delta-24}{5}u+1.
\]

These generators are related exactly by
\[
\boxed{
Q(1+\epsilon^3u)=\epsilon^6S(u).
}
\]

Moreover, \(Q\) and PARI's relative class-field polynomial define the same quadratic extension, and
\[
\mathfrak D_{K_{11}(t)/K_{11}}=\mathfrak p_+,
\qquad
\mathfrak f=\mathfrak p_+\infty_+.
\]

Thus the secondary branch is exactly the simple quadratic ray field, and its displayed HI generator is an affine transform of PARI's norm-one Stark unit.

## 22.2 Principal branch: the missing prime over \(5\)

Refining the published Evans–Gannon phase seed and recognizing the orbit of
\[
\eta=-B_{g,2g}^2/\delta
\]
gives the reciprocal polynomial
\[
P_\eta(X)=X^{10}+c_1X^9+c_2X^8+c_3X^7+c_4X^6+c_5X^5
           +c_4X^4+c_3X^3+c_2X^2+c_1X+1,
\]
where
\[
\begin{aligned}
c_1&=144\delta-1597,\\
c_2&=854377-77039\delta,\\
c_3&=15771418\delta-174907704,\\
c_4&=13808071707-1245073049\delta,\\
c_5&=27511525729\delta-305107495744.
\end{aligned}
\]

The reproducible 100-digit refinement in `z11_stark_test.gp` gives residuals below \(4.2\times10^{-100}\) over every instance of (4.2) and all \(11^4\) instances of (4.3), and a maximum coefficient error below \(6.4\times10^{-99}\). A separate 180-digit run gives corresponding bounds \(3.7\times10^{-181}\) and \(3.6\times10^{-170}\). Polynomial recognition is the sole numerical-to-exact step; once this reconstructed polynomial is accepted as input, all following statements are exact PARI calculations:

- \(P_\eta\) is irreducible over \(K_{11}\);
- if \(\mathfrak q_5\) is the ramified prime above \(5\), then
  \[
  \boxed{
  \mathfrak f
  =\mathfrak p_+\mathfrak q_5^2\infty_+
  =5\mathfrak p_+\infty_+;
  }
  \]
- the full ray group for this conductor is \(C_{10}\), and \(P_\eta\) defines the full ray field rather than a proper quotient;
- the relative discriminant is
  \[
  \mathfrak D=\mathfrak q_5^{16}\mathfrak p_+^9;
  \]
- the absolute discriminant is
  \[
  -5^{26}11^9
  =-3513615863025188446044921875.
  \]

This confirms the earlier guess that the ramified prime over \(5\) distinguishes the principal branch. The identification is still conditional on the numerical-to-exact reconstruction of \(P_\eta\), so an independent reconstruction or direct verification of the Izumi equations remains desirable.

---

# 23. Explicit Shintani–Faddeev parameters for the HI ray classes

Kopp's ray-class/RM-point correspondence can be specialized explicitly to the HI fields. This is a derivation from Theorem 3.14 and Theorem 8.2 of [arXiv:2411.06763](https://arxiv.org/abs/2411.06763), not a formula stated there specifically for Haagerup–Izumi data.

View \(K_p\) through the real embedding \(\rho_1(\delta)=\delta_-<0\), leaving the physical place as Kopp's distinguished second embedding, and put
\[
\beta=-\delta=\delta_+^{-1}>0,
\qquad
M=\begin{pmatrix}1&p\\p&p^2+1\end{pmatrix},
\qquad
\mathbf r_u=-\frac{u}{p}\binom11.
\]

Then
\[
M\beta=\beta,
\qquad
j_M(\beta)=\beta^{-2}>1,
\qquad
M\equiv I\pmod p.
\]

Kopp's denominator parameter becomes
\[
[[\mathbf r_u,\beta]]
=\frac{u(1-\beta)}p
=\frac{u(1+\delta)}p
=\frac{u\delta}{\delta-1},
\]
so its denominator ideal is exactly \(\mathfrak p_+=(\delta-1)\). Taking the totally positive generator
\[
\alpha=\delta(\delta-1)
\]
of \(\mathfrak p_+\), the correspondence produces
\[
\gamma_u
=\alpha[[\mathbf r_u,\beta]]
=u\delta^2
\equiv u\pmod{\mathfrak p_+}.
\]

Thus the characteristics \(\mathbf r_u\), for \(u\in\mathbb F_p^\times\), carry exactly the desired residue-class labeling. For \(p=17\), they exhaust the sixteen ray classes.

For this specialization the theta and eta multiplier factors simplify to \(1\). Since the two-infinite-place to one-infinite-place ray-class map has trivial fiber at \(p=17\), Kopp's formula becomes
\[
\exp\!\left(2Z'(0,\mathfrak A_u)\right)
=
\operatorname{shin}^{\mathbf r_u}_M(\beta)^2.
\]

This also explains why the sign in
\[
\varepsilon_{\mathrm{HI}}=-U^2
\]
is natural: at \(\rho_1\), \(\delta<0\), so \(U=B/\sqrt\delta\) is imaginary and \((iU)^2=-U^2\).

The exact algebraic comparisons at \(p=7,13,17\) now identify the quotient automorphism by reduction at \((2)\): after a compatible Galois shift of the Stark root,
\[
\boxed{
e_u^2=\frac{s_u^2}{\operatorname{Frob}_{(2)}(s_u)}.
}
\]
After a compatible identification of the HI multiplier orbit with the displayed residue-class labeling, this reads \(e_u^2=s_u^2/s_{2u}\), up to the global arithmetic-versus-geometric Artin convention. That individual-root alignment is not encoded by the present minimal-polynomial tests. The next analytic computation is therefore sharper: evaluate Kopp's Shintani–Faddeev values for the displayed \((M,\beta,\mathbf r_u)\), fix their root normalization and Artin convention, and determine whether this exact Frobenius quotient is a standard cocycle or distribution relation.

---

# 24. Exact \(p=7\) comparison

The \(p=7\) case can be derived without numerical reconstruction. Evans–Gannon's proof of Theorem 5(d) in [arXiv:1006.1326](https://arxiv.org/abs/1006.1326) gives an exact construction of the entry
\[
a=B_{1,2}.
\]

Eliminating their auxiliary quadratic element \(b\) from the displayed cubic for \(a\) gives
\[
\begin{aligned}
P_a(W)={}&W^6-W^5+(\delta-7)W^4+(9-3\delta)W^3+W^2\\
&-(7\delta+1)W+(50\delta+7).
\end{aligned}
\]

For \(e=-a^2/\delta\), exact elimination yields
\[
\boxed{
\begin{aligned}
E_7(X)={}&X^6+(15\delta-107)(X^5+X)\\
&+(-503\delta+3591)(X^4+X^2)\\
&+(5153\delta-36794)X^3+1.
\end{aligned}
}
\]

For
\[
K_7=\mathbb Q(\delta),
\qquad
\delta^2-7\delta-1=0,
\qquad
\mathfrak p_+=(\delta-1),
\]
PARI gives
\[
\operatorname{Cl}_{\mathfrak p_+\infty_+}(K_7)\simeq C_6.
\]

Its `bnrstarkunit` polynomial is
\[
\begin{aligned}
S_7(X)={}&X^6+(19\delta-137)(X^5+X)\\
&+(-503\delta+3591)(X^4+X^2)\\
&+(1635\delta-11672)X^3+1.
\end{aligned}
\]

As at \(p=17\):

- \(E_7\neq S_7\), and no HI root is pure-power-related to an individual Stark conjugate;
- both polynomials are irreducible and define exactly the same relative field;
- both fields have relative discriminant \(\mathfrak p_+^5\);
- for compatible roots \(e,s\) and a generator \(\sigma\in C_6\),
  \[
  \boxed{
  e^2=\frac{s^2}{\sigma^2(s)}.
  }
  \]

Equivalently, \(e^2=s^2/\rho(s)\) for a generator \(\rho\) of the order-three subgroup \(G^2\). Because the HI input here is exact, this proves that the quotient pattern is not an artifact of the \(p=17\) numerical reconstruction.

Here too the quotient automorphism is determined intrinsically. The prime \((2)\) is inert with norm \(4\), and exact reduction in the common field gives
\[
\rho(s)\equiv s^4\pmod 2.
\]
Thus
\[
\rho=\operatorname{Frob}_{(2)},
\qquad
\operatorname{ord}(\rho)=3=\operatorname{ord}_7(2).
\]

All statements are reproduced by `z7_stark_test.gp`, including a certified base-field class/unit computation.

---

# 25. Completed \(p=13\) comparison and the Frobenius-\(2\) law

The \(p=13\) input begins with the Evans–Gannon numerical seed from Section 4.1 of [arXiv:1006.1326](https://arxiv.org/abs/1006.1326),
\[
j^{(13)}=(-3.1050384,\,0.5993399,\,-0.111708,\,-0.969766,\,1.336848,\,1.00483129).
\]
Six independent instances of their equation (4.2) refine these phases to 180 digits. All instances of (4.2), and all \(13^4\) instances of (4.3), then have numerical residual below \(3.7\times10^{-181}\). The script records 100 digits of the refined solution and recomputes the complete systems with residual below \(3.1\times10^{-100}\); its maximum coefficient error is \(1.1\times10^{-96}\). Thus polynomial recognition is the only numerical-to-exact step below.

For
\[
K_{13}=\mathbb Q(\delta),
\qquad
\delta^2-13\delta-1=0,
\qquad
e=-B_{g,2g}^2/\delta,
\]
the recognized orbit polynomial is
\[
E_{13}(X)=X^{12}+\sum_{j=1}^{5}c_j(X^{12-j}+X^j)+c_6X^6+1,
\]
where
\[
\begin{aligned}
c_1&=467\delta-6097,\\
c_2&=12814191-979939\delta,\\
c_3&=825835784\delta-10799019382,\\
c_4&=3392673833885-259448689016\delta,\\
c_5&=30448109649290\delta-398153890397194,\\
c_6&=11724621314790962-896619533298169\delta.
\end{aligned}
\]

The following statements are then exact:

- the physical ray group is
  \[
  \operatorname{Cl}_{(\delta-1)\infty_+}(K_{13})\simeq C_{12};
  \]
- \(E_{13}\) is irreducible and reciprocal, and its field has conductor exactly \((\delta-1)\infty_+\), so it is the full ray field;
- the relative discriminant is \((\delta-1)^{11}\);
- the absolute discriminant and signature are
  \[
  173^{12}13^{11}
  =1288042262034535290413536071230037719077,
  \qquad
  (r_1,r_2)=(12,6);
  \]
- PARI's degree-twelve Stark polynomial is different from \(E_{13}\), but the two absolute fields admit twelve \(K_{13}\)-preserving isomorphisms.

For a compatible HI root \(e\), Stark root \(s\), and one order-twelve generator \(\tau\), the exhaustive exact two-conjugate search finds one relation per HI conjugate, always with the same displacement. One representative is
\[
e^2=\frac{\tau^8(s)^2}{\tau(s)}.
\]
Putting \(s_0=\tau^8(s)\) and \(\rho=\tau^5\) gives
\[
\boxed{
e^2=\frac{s_0^2}{\rho(s_0)}.
}
\]

Finally, \(2\) is inert in \(K_{13}\), the prime \(\mathfrak q_2=(2)\) has norm \(4\), and its ray class generates \(C_{12}\). Exact reduction gives
\[
\rho(s)\equiv s^4\pmod{\mathfrak q_2},
\]
so
\[
\rho=\operatorname{Frob}_{\mathfrak q_2},
\qquad
\operatorname{ord}(\rho)=12=\operatorname{ord}_{13}(2).
\]

Together, the three completed cases give
\[
\begin{array}{c|c|c}
p & \operatorname{ord}_p(2) & \operatorname{ord}(\operatorname{Frob}_{(2)})\\ \hline
7&3&3\\
13&12&12\\
17&8&8
\end{array}
\]
and, more strongly than this order coincidence, the reduction calculations identify the field automorphism itself. After choosing a compatible identification between the HI multiplier orbit and the ray-class labels, the resulting sharpened conjecture is
\[
\boxed{
e_u^2=\frac{s_u^2}{s_{2u}}.
}
\]
The field-theoretic statement using \(\operatorname{Frob}_{(2)}\) is exact. Two labeling points remain to be fixed analytically: whether a chosen reciprocity map labels arithmetic Frobenius by \(2\) or \(2^{-1}\), and which individual HI root carries the ray label \(u=1\).

All exact checks, together with the recorded 100-digit reconstruction test, are reproduced by `z13_stark_test.gp`.

---

# 26. The two \(p=19\) branches and the Hilbert class field

The class-number-two case now admits a precise explanation. Put
\[
K=K_{19}=\mathbb Q(\delta),
\qquad
\delta^2-19\delta-1=0,
\qquad
\mathfrak p=(\delta-1).
\]
PARI certifies
\[
\operatorname{Cl}(K)\simeq C_2,
\]
and the physical ray group is
\[
\boxed{
\operatorname{Cl}_{\mathfrak p\infty_+}(K)
\simeq C_{18}\times C_2.
}
\]
Thus the order is \(36\), as predicted earlier, but the group is not cyclic.

## 26.1 The residue-(2) subgroup and the class-group quotient

The prime \(\mathfrak q_2=(2)\) is inert in \(K\), with norm \(4\). In PARI's displayed \(C_{18}\times C_2\) coordinates its ray class is \([10,1]\), of order
\[
18=\operatorname{ord}_{19}(2).
\]
Because \((2)\) is principal, its class lies in the kernel of the natural map
\[
\operatorname{Cl}_{\mathfrak p\infty_+}(K)
\longrightarrow
\operatorname{Cl}(K).
\]
Both that kernel and \(\langle\operatorname{Frob}_{(2)}\rangle\) have order \(18\), so they are equal. Moreover,
\[
\operatorname{Frob}_{(2)}^9=c,
\]
where \(c\) is complex conjugation; this is the class-field version of \(2^9\equiv-1\pmod {19}\).

The fixed field of this order-eighteen subgroup is the Hilbert class field
\[
H=K\!\left(\sqrt{58-3\delta}\right)
  =\mathbb Q(\sqrt5,\sqrt{73}).
\]
PARI gives the relative and absolute equations
\[
X^2+3\delta-58,
\qquad
X^4-59X^2+49,
\]
and \(\operatorname{disc}(H)=365^2\), confirming that \(H/K\) is everywhere unramified.

This makes the two-branch mechanism nearly forced: the two cosets of the subgroup generated by Frobenius at \(2\) are exactly the two ordinary ideal classes. The nontrivial class involution exchanges the cosets, while Frobenius at \(2\) moves transitively inside each one.

The full ray field \(L/K\) has
\[
\mathfrak D_{L/K}=\mathfrak p^{34},
\qquad
|\operatorname{disc}L|=365^{36}19^{34},
\qquad
(r_1,r_2)=(36,18).
\]
PARI's full `bnrstarkunit` polynomial is irreducible, reciprocal, and of degree \(36\). If \(s\) is one of its roots, the trace \(s+s^{-1}\) has an irreducible degree-eighteen polynomial whose field is exactly the finite-ray, maximal totally real subfield; its relative discriminant is \(\mathfrak p^{16}\).

## 26.2 Reconstruction of the two HI branches

Both Evans–Gannon \(p=19\) phase seeds were Newton-refined to 450 digits. The regression script retains about 115 digits and checks every instance of equations (4.2) and (4.3) for both branches. From the two \(t=2\) orbits, set
\[
e=-B_{u,2u}^2/\delta.
\]
Their combined orbit has the reciprocal polynomial
\[
E_{19}(X)
=X^{36}+\sum_{j=1}^{17}c_j(X^{36-j}+X^j)+c_{18}X^{18}+1.
\]
The full coefficient list is recorded in `z19_stark_test.gp`; useful fingerprints are
\[
\begin{aligned}
c_1={}&-333455+17502\delta,\\
c_{18}={}&313454105109270988272887994762348265080330293\\
&-16452136243396368439735966221635671877278307\delta.
\end{aligned}
\]

Polynomial recognition is the only numerical-to-exact step. Once \(E_{19}\) is accepted, exact PARI calculations show that it is irreducible over \(K\), has conductor exactly \(\mathfrak p\infty_+\), has trivial norm subgroup in \(C_{18}\times C_2\), and has relative discriminant \(\mathfrak p^{34}\). It therefore defines the full ray field. It differs from PARI's Stark polynomial, but both generators define the unique full ray extension attached to the same conductor and norm subgroup.

Each branch separately becomes algebraic over \(H\), not over \(K\). If \(w,w'\) are the first nontrivial coefficients of the two conjugate degree-eighteen branch polynomials, then
\[
w+w'=-333455+17502\delta,
\]
\[
ww'=61207710-3212584\delta.
\]
The resulting quadratic coefficient field is unramified over \(K\) and reduces to
\[
X^2+\delta-29;
\]
it is the same Hilbert class field \(H\). All remaining branch coefficients were recognized in \(K(w)\), and their exact Hilbert conjugate norm is \(E_{19}\).

This is a direct arithmetic realization of the old branch hypothesis:
\[
\boxed{
\text{the two HI branches are the two Hilbert-class conjugate halves of one ray-class orbit.}
}
\]
It also explains why Evans–Gannon's second modular-data label involves the pair \(\{5,73\}\): these are precisely the two prime-discriminant factors whose genus field is \(\mathbb Q(\sqrt5,\sqrt{73})\).

## 26.3 Status of the Stark quotient at \(p=19\)

A high-precision all-pairs root search finds exactly \(36\) matches of the form
\[
e_k^2=\frac{s_i^2}{s_j}.
\]
The selected edges form a permutation of the Stark roots with cycle lengths \([18,18]\), and its ninth power sends every root to its inverse. This is exactly the cycle signature of a generator of
\[
\langle\operatorname{Frob}_{(2)}\rangle
=\ker\!\left(\operatorname{Cl}_{\mathfrak p\infty_+}(K)\to\operatorname{Cl}(K)\right).
\]
This comparison is numerical, unlike the exact reductions modulo \(2\) at \(p=7,13,17\). It does not yet distinguish \(\operatorname{Frob}_{(2)}\) from another generator of the same cyclic subgroup. The branchwise conjecture is therefore
\[
\boxed{
e_{b,u}^2
=\frac{s_{b,u}^2}{s_{b,2u}},
\qquad
b\in\operatorname{Cl}(K)\simeq C_2,
}
\]
subject to exact Artin/root alignment.

The exact ray arithmetic is reproduced by `z19_ray_test.gp`; the numerical reconstruction and exact downstream HI-field checks are in `z19_stark_test.gp`.

---

# 27. Group-ring and Shintani–Faddeev reformulation

The quotient law now has a useful intrinsic form. Let
\[
G=\operatorname{Gal}(L/K),
\qquad
\phi=\operatorname{Frob}_{(2)},
\qquad
H=\langle\phi\rangle,
\qquad
t=e^2.
\]
With multiplicative group-ring notation, the exact \(p=7,13,17\) relation is
\[
\boxed{
t=s^{\Theta_2},
\qquad
\Theta_2=2-\phi.
}
\]
The opposite Artin convention replaces \(\phi\) by \(\phi^{-1}\).

## 27.1 Why the operator loses no field information

If \(d=\operatorname{ord}(\phi)\), define
\[
\Psi_d=2^{d-1}+2^{d-2}\phi+\cdots+\phi^{d-1}.
\]
Then
\[
(2-\phi)\Psi_d=2^d-\phi^d=2^d-1,
\]
and hence
\[
t^{\Psi_d}=s^{2^d-1}.
\]
On each \(H\)-coset,
\[
\operatorname{coker}\!\left(
\mathbb Z[H]\xrightarrow{\,2-\phi\,}\mathbb Z[H]
\right)
\simeq \mathbb Z/(2^d-1),
\]
while characterwise the eigenvalues are \(2-\chi(\phi)\), none of which vanish. Because the ray fields here have a real embedding, their only roots of unity are \(\{\pm1\}\); since \(2^d-1\) is odd, the relation implies
\[
K(s)=K(e^2).
\]
This gives a conceptual reason, independent of polynomial reduction, that the Frobenius quotient still generates the full Stark field.

It is important not to call \(t\) uniformly a Hilbert–90 coboundary. What is always a coboundary is
\[
\frac ts=\frac{s}{\phi(s)}=s^{1-\phi},
\]
so \(N_H(t)=N_H(s)\). At \(p=13\) and \(17\) this subgroup norm is \(1\). At \(p=7\) it is not: the exact absolute polynomial of \(N_H(s)\) is
\[
X^4-932X^3+70X^2-932X+1.
\]
These norm assertions are now included in the corresponding GP scripts.

## 27.2 A sharper analytic candidate

Kopp defines the Shintani–Faddeev modular cocycle on the upper half-plane by
\[
\operatorname{shin}^{\mathbf r}_{A}(\tau)
=\frac{\varpi_{\mathbf r}(A\tau)}{\varpi_{\mathbf r}(\tau)}.
\]
For the odd-denominator characteristics \(\mathbf r_u\) of Section 23,
\[
\Gamma_{\mathbf r_u}=\Gamma_{2\mathbf r_u}.
\]
Therefore
\[
D^{\mathbf r}_{2,A}(\tau)
:=
\frac{\operatorname{shin}^{\mathbf r}_{A}(\tau)^2}
     {\operatorname{shin}^{2\mathbf r}_{A}(\tau)}
\]
is itself a modular \(1\)-cocycle. On the upper half-plane it is the literal coboundary of
\[
F^{\mathbf r}_2(\tau)
=\frac{\varpi_{\mathbf r}(\tau)^2}{\varpi_{2\mathbf r}(\tau)}.
\]
As with Kopp's original cocycle, extension to the larger domain containing an RM boundary point can leave a nontrivial cohomology class.

Under the Stark normalization in Section 23,
\[
s_u=\operatorname{shin}^{\mathbf r_u}_{M}[\beta]^2
\]
up to the already noted inversion and multiplier conventions. Consequently
\[
\left(D^{\mathbf r_u}_{2,M}[\beta]\right)^2
=\frac{s_u^2}{s_{2u}}.
\]
The algebraic result therefore suggests the unsquared formula
\[
\boxed{
e_u
=\pm
\frac{\operatorname{shin}^{\mathbf r_u}_{M}[\beta]^2}
     {\operatorname{shin}^{2\mathbf r_u}_{M}[\beta]}.
}
\]
This characteristic-difference cocycle is a substantially sharper analytic target than a literal Stark-unit equality.

It is not Kopp's conductor-lowering relation in disguise. Theorem 4.46 applied to doubling uses a determinant-four matrix and a product over four half-characteristics; standard arithmetic smoothing at the inert ideal \((2)\) likewise has weight \(N(2)=4\). The observed operator \(2-\phi\) is instead a square-root, or weight-one, analogue. Establishing the algebraicity, sign, and Shimura-reciprocity law of this unsquared RM value appears to be the genuinely new theorem required.

More generally, for \(c\) coprime to \(p\), put
\[
D_{c,u}=\frac{q_u^c}{q_{cu}},
\qquad
\Theta_c=c-\sigma_c.
\]
Then the formal identities
\[
\Theta_{ab}=b\Theta_a+\sigma_a\Theta_b,
\qquad
D_{ab,u}=D_{a,u}^{\,b}D_{b,au}
\]
give a weighted semigroup distribution law. Whether the other HI ratio types \(B_{u,cu}\) realize these \(D_c\) is now a concrete test rather than a vague search for unit relations.

The best first analytic experiment is the exact \(p=7\) case: evaluate \(D_{2,M}^{\mathbf r_1}[\beta]\), fix its sign and Artin orientation against the known algebraic HI root, and only then attempt a proof from quantum-dilogarithm or theta identities.

---


---

# 28. A diagonal-determination theorem for the full fourth-power core

The short Frobenius law contains more information than Section 14 suggested.
The following argument is algebraic and works for every finite abelian group
of odd order. It requires a **labeled** doubling law in a common field;
equality of orbit polynomials alone does not supply that hypothesis.

## 28.1 Correct cyclic phase normalization

The Evans–Gannon phases in Section 4 are initially given for integer
representatives \(0<g<h<n\). Put \(r=(n-1)/2\) and
\(C=j_r+j_{r+1}\). Their extension rule says \(j_{n-g}=C-j_g\).
The periodic phases to use in identities on \(\mathbb Z_n\) are
\[
 z_0=1,\qquad z_g=\exp\!\left(i(j_g-Cg/n)\right),\quad 1\le g<n.
\]
Then \(z_{-g}=z_g^{-1}\), and the generic formula
\(U_{g,h}=z_h/(z_gz_{h-g})\) holds with indices reduced modulo \(n\).
Using the raw published \(e^{ij_g}\) as a periodic sequence would miss
the correction at wraparound.

Define an auxiliary normalized cocycle
\[
 C(a,b)=\frac{z_{a+b}}{z_az_b},\qquad V(a,b)=C(a,b)^4.
\]
Thus \(C(a,b)=U_{a,a+b}\) when \(a,b,a+b\ne0\), while
\(C(a,0)=C(0,a)=C(a,-a)=1\). These auxiliary boundary values are
**not** the actual exceptional scaled matrix entries.

Both cocycles are symmetric and satisfy
\[
 V(a,b)V(a+b,c)=V(b,c)V(a,b+c).
\]

## 28.2 Diagonal determination

**Proposition.** Let \(V\) be a normalized symmetric multiplicative
\(2\)-cocycle on a finite abelian group \(G\) of odd order, taking values
in a number field \(L\) with a real embedding. Suppose \(s_a\in L^\times\),
\(s_0=1\), and
\[
 V(a,a)=s_a^2/s_{2a}\quad(a\in G).
\]
Then
\[
 \boxed{V(a,b)=s_as_b/s_{a+b}\quad(a,b\in G).}
\]

**Proof.** Divide \(V\) by the symmetric cocycle
\(R(a,b)=s_as_b/s_{a+b}\), obtaining \(W\) with \(W(a,a)=1\).
For any symmetric cocycle, comparing the two groupings of
\((a,a,b,b)\) gives
\[
 W(2a,2b)=W(a,b)^2
 \frac{W(a+b,a+b)}{W(a,a)W(b,b)}=W(a,b)^2.
\]
Choose \(d\) such that multiplication by \(2^d\) is the identity on
\(G\). Iteration yields \(W(a,b)^{2^d-1}=1\). A field with a real
embedding has only the roots of unity \(\{\pm1\}\), and \(2^d-1\)
is odd. Hence \(W(a,b)=1\). ∎

In particular, assuming the common-field and labeling hypotheses, the
doubling law in Section 27 implies the **entire** generic formula
\[
 \boxed{
 U_{g,h}^4=\frac{s_gs_{h-g}}{s_h},\qquad
 B_{g,h}^4=\delta^2\frac{s_gs_{h-g}}{s_h}.
 }
 \tag{28.1}
\]
For \(h=2g\), this is precisely \(e_g^2=s_g^2/s_{2g}\).
The formula is compatible with rotation and with reflection/conjugation
when \(s_{-g}=s_g^{-1}\). Section 29 verifies it with exact labels,
for all entries, in the five completed cases.

This argument neither assumes a primitive root \(2\) nor assumes that
\(\delta\) is fundamental or that the base class number is one.
It also explains why a field hypothesis matters: in \(\mathbb C^\times\)
alone there can be odd-order torsion ambiguities.

## 28.3 Correction to the proposed higher-multiplier formula

For an integer \(2\le c<n\) and a unit \(g\bmod n\), (28.1) gives
\[
 U_{g,cg}^4=\frac{s_gs_{(c-1)g}}{s_{cg}}.
\]
In contrast, telescoping gives
\[
 \boxed{
 \prod_{j=1}^{c-1}U_{g,(j+1)g}^4=\frac{s_g^c}{s_{cg}}.
 }
 \tag{28.2}
\]
Thus the weighted operator \(c-\sigma_c\) at the end of Section 27
describes a product of adjacent generic entries. Its identification with
a single ratio type is appropriate only at \(c=2\), unless an additional
special identity holds. Formula (28.1), with three Stark factors, is the
uniform expression for individual entries.

---

# 29. Exact construction from Stark polynomials without HI seeds

The new file [`hi_stark_seedless.gp`](hi_stark_seedless.gp) starts with
\[
 S=\operatorname{bnrstarkunit}
 \left(K_n,\,(\delta-1)\infty_+\right)
\]
and constructs a full matrix over its field. There is no numerical HI
seed, Newton iteration, coefficient recognition, or numerical root
selection in this construction.

PARI's general analytic Stark interpretation remains conjectural. That
does not make these **finite existence certificates** conditional:
the returned polynomial supplies exact algebraic input, and the
constructed matrix is checked against the complete defining equations.
An incorrect analytic guess would simply fail those checks.

The precise construction is as follows.

1. Certify the quadratic class/unit computation and check the returned
   polynomial's irreducibility, conductor, and full ray degree. Express
   its root \(s\) and \(\delta\) in an absolute number field \(L\).
2. Choose a small prime \(\ell\) inert in \(K_n\) that generates
   \(\mathbb F_n^\times\). Identify arithmetic Frobenius at \((\ell)\)
   by reduction of **every integral-basis element** at a prime above
   \(\ell\). This avoids relying on a particular polynomial having
   index coprime to \(\ell\).
3. Set \(s_{\ell^j}=\phi^j(s)\) and \(s_0=1\). Repeated ray labels are
   permitted: at \(n=11,29\), \(\phi\) has smaller order than \(n-1\).
4. For \(2\le h\le(n+1)/2\), find the roots **inside \(L\)** of
   \[
    X^4-\delta^2s_1s_{h-1}/s_h.
   \]
   There are exactly two, differing by sign, in each completed case.
   Initially select either one. Set \(B_{1,n+1-h}=B_{1,h}\).
5. Define \(P_1=1\), \(P_h=\prod_{j=2}^hB_{1,j}\). Reconstruct
   \[
    \boxed{B_{g,h}=P_h/(P_gP_{h-g})\quad(0<g<h<n).}
    \tag{29.1}
   \]
   Extend by conjugation, and insert the exceptional entries from
   Section 4. No square root of \(\delta\) is needed in (29.1).
6. Use the sign-transport theorem in Section 30 to impose
   \(\phi(B_{g,h})=B_{\ell g,\ell h}\), and check the resulting
   linear system over \(\mathbb F_2\). Exactly one global generic
   sign remains. Test its two choices against the quadratic equations.
7. Verify rotation, conjugation, generic norms, every formula (28.1),
   and the full quadratic and cubic Izumi systems, with exact field
   arithmetic.

To justify physical unitarity rather than just a formal involution,
the script proves that \(s+s^{-1}\) generates a totally real subfield
of index two, that \(\phi^{(n-1)/2}(s)=s^{-1}\), and that every real
embedding of \(L\) has \(\delta<0\). Therefore this involution is actual
complex conjugation at the physical embeddings \(\delta>0\).
The checked identities \(B_{g,h}\overline{B_{g,h}}=\delta\) give the
required positive physical norms.

## 29.1 Completed exact certificates

The full results are recorded in
[`hi_stark_seedless_results.txt`](hi_stark_seedless_results.txt).

| \(n\) | ray group | \([L:\mathbb Q]\) | rank of sign system | cubic representatives checked |
|---:|---|---:|---:|---:|
| 7 | \(C_6\) | 12 | 2 | 401 |
| 11 | \(C_2\) | 4 | 4 | 1465 |
| 13 | \(C_{12}\) | 24 | 5 | 2381 |
| 17 | \(C_{16}\) | 32 | 7 | 5221 |
| 29 | \(C_4\) | 8 | 13 | 25261 |

The cubic counts cover **every** quadruple: after verifying multiplier
covariance, each nonzero \((g,h,k,l)\) has a unique scalar multiple
whose first nonzero coordinate is \(1\). Include the zero quadruple.
The count is
\[
 1+\frac{n^4-1}{n-1}=n^3+n^2+n+2.
\]
The script uses the scaled equations
\[
 \sum_j B_{g+j,h}\overline{B_{j,h}}
 = (\delta-1)^2\left(\mathbf1_{g=0}-\frac{\mathbf1_{h=0}}\delta\right),
 \tag{29.2}
\]
\[
 \begin{split}
 \sum_j B_{j,g+h}\overline{B_{j+k,g}B_{j+l,h}}
 ={}&(\delta-1)B_{g+l,k}B_{h+k,l}\\
 &-\frac{(\delta-1)^3}{\delta}\mathbf1_{g=0}\mathbf1_{h=0}.
 \end{split}
 \tag{29.3}
\]
Together with the checked symmetries, these are exactly the
Evans–Gannon/Izumi conditions. Their sufficiency for the corresponding
subfactor and HI fusion rules is the result used from
[Evans–Gannon, Section 4.1 and Theorem 6](https://arxiv.org/html/1006.1326#S4).

These are certificates of the construction in this repository, not a
claim that existence at these five orders is new to the literature.

## 29.2 Removal of numerical-recognition assumptions

As **downstream** checks, the script proves:

- at \(n=11\), its \(B_{1,2}\) satisfies
  \(X^2+(3\delta-4)X/5+\delta\), identifying the simple-ray secondary
  branch of Section 22.1;
- at \(n=13\), the exact product
  \(\prod_{g\ne0}(X+B_{g,2g}^2/\delta)\) is exactly \(E_{13}\) of
  Section 25;
- at \(n=17\), all three exact products
  \(\prod_{g\ne0}(X-B_{g,tg})\), \(t=2,3,4\), agree with
  `z17_haagerup_izumi_minpolys.sage`.

Thus the old recognized polynomials really occur in complete exact
HI solutions. Their downstream field identifications no longer require
an assumption that the numerical phases were correctly recognized.
The principal \(n=11\) branch retains its previously stated
qualification. The later exact order-19 certificate and polynomial
assertions in Section 35.2 discharge the order-19 recognition issue.

## 29.3 Small explicit inputs for the fixed-field family

The two certificates over \(K=\mathbb Q(\sqrt5)\) start from particularly
small polynomials. With \(\epsilon=(1+\sqrt5)/2\), PARI returns
\[
 S_{11}(X)=X^2+(3\epsilon-3)X+1,
\]
\[
 S_{29}(X)=X^4+(14\epsilon-21)(X^3+X)
                    +(45-27\epsilon)X^2+1.
\]
Here \(\delta_{11}=\epsilon^5\) and
\(\delta_{29}=\epsilon^7\). Applying the construction above yields
complete exact matrices over fields of absolute degrees 4 and 8.
These two cases show concretely that a nonfundamental \(\delta\) and
the resulting collapse of residue labels are compatible with the
full fourth-power formula and exact sum identities.

## 29.4 The earlier class-number-two checkpoint, now completed

A bounded \(n=19\) run completed the exact field, Frobenius-label,
and physical-conjugation checks, and found both roots inside the
degree-72 absolute ray field for each of the nine independent row
quartics, \(2\le h\le10\). The transcript is
[`hi_stark19_partial_results.txt`](hi_stark19_partial_results.txt).
The run reached its ten-minute limit before completing matrix
verification. That bounded run alone was not a full certificate.
Section 35.2 records its completed continuation, including every cubic
equation and the exact identification of the earlier branch polynomial.

---

# 30. Why the sign problem has only one binary degree of freedom

The observed ranks in Section 29 have a structural explanation.

**Proposition.** Let \(p\) be odd prime. Suppose two normalized phase
cocycles \(C,C'\) on \(\mathbb Z_p\) have \(C(a,-a)=C'(a,-a)=1\).
Suppose their corresponding generic \(B\)-entries lie in a common
number field with a real embedding, have the same fourth powers, and
are equivariant for one automorphism implementing a primitive scalar
\(\ell\bmod p\). Then their generic entries agree everywhere, or all
differ by the same sign.

**Proof.** Their ratio \(W=C'/C\) is a normalized symmetric cocycle
with values in \(\{\pm1\}\). Write \(D(a)=W(a,a)\). The duplication
identity from Section 28 gives
\[
 W(2a,2b)=D(a+b)D(a)D(b).
\]
Since doubling is invertible, the function \(f(a)=D(a/2)\) satisfies
\[
 W(a,b)=f(a)f(b)/f(a+b).
\]
Equivariance fixes the signs, so \(W(\ell a,\ell b)=W(a,b)\).
Consequently \(f(\ell a)/f(a)\) is a homomorphism
\(\mathbb Z_p\to\{\pm1\}\), which is trivial. The scalar \(\ell\)
is transitive on nonzero indices; hence \(f\) is constant there.
Its value is either \(1\) or \(-1\). The associated coboundary equals
that value on every generic pair. ∎

This first proposition is an **at-most-two** statement. Under the
quartic-lift hypotheses of the construction, consistency also has a
uniform proof.

**Sign-transport proposition.** Suppose the arbitrary initial row
roots in Section 29 exist in \(L\), the labeled \(s_a\) have physical
modulus one, \(L\) has a real embedding with \(\delta<0\), and
\(\phi^{(p-1)/2}\) is physical complex conjugation.
Then signs making the reconstructed matrix scalar-equivariant exist.
They are determined up to the global generic sign above.

**Proof.** The row roots have physical modulus \(\sqrt\delta\).
Their reflection symmetry \(B_{1,h}=B_{1,p+1-h}\) permits a unit
phase sequence with \(z_{-a}=z_a^{-1}\): apply the prefix recursion
and choose \(z_1\) to close the cyclic sequence. Thus the initial
matrix defines a normalized phase cocycle \(C\).

Extend \(\phi\) to fix \(\sqrt\delta\). This is legitimate because
\(\sqrt\delta\notin L\): at a real embedding of \(L\) the element
\(\delta\) is negative. In particular the extension still satisfies
\(\phi^{(p-1)/2}=\) physical conjugation. Put
\[
 E(a,b)=\frac{\phi(C(a,b))}{C(\ell a,\ell b)}.
\]
The fourth-power formula shows \(E(a,b)^4=1\); the square roots of
\(\delta\) cancel in this quotient, so \(E(a,b)\in L\) and hence
\(E(a,b)\in\{\pm1\}\). It is a symmetric normalized cocycle.
As above,
\[
 E(a,b)=f(a)f(b)/f(a+b),\qquad f(a)=E(a/2,a/2).
\]
Write \(r=(p-1)/2\). Iterating the error equation \(r\) times gives
\[
 \prod_{j=0}^{r-1}E(\ell^j a,\ell^j b)
 =\frac{\overline{C(a,b)}}{C(-a,-b)}=1.
\]
Therefore \(F(a)=\prod_{j=0}^{r-1}f(\ell^j a)\) is a homomorphism
\(\mathbb Z_p\to\{\pm1\}\), so \(F(a)=1\).
Define \(t_0=1\), choose \(t_1=1\), and transport signs by
\[
 \boxed{t_{\ell a}=f(a)t_a.}
\]
The half-orbit product just proved ensures \(t_{-a}=t_a\) and
closure of the full orbit. Replacing \(C(a,b)\) by
\(C(a,b)t_at_b/t_{a+b}\) kills its covariance error and preserves
the normalization and conjugation conditions. ∎

Thus root-sign compatibility is not a further conjecture in prime
order once these field and fourth-root hypotheses are available.
Neither proposition asserts that the quadratic or cubic sum
identities hold; those remain separate requirements.

The row algorithm also makes the constraints explicit. There are
\((p-1)/2\) initial row signs. Formula (29.1) expresses the sign of
every entry as a linear expression in their bits. Comparing scalar
translates gives a linear system over \(\mathbb F_2\), of rank
\((p-3)/2\) in every completed case. The script constructs its
solution by the transport formula, checks every linear equation,
and verifies the rank. This replaces a search over
\(2^{(p-1)/2}\) phase choices with sign transport and two final tests.

For composite \(n\), multiplication by units is not transitive on
all nonzero residues. The prime-order conclusion must not be used
unchanged: additional sign freedoms can occur on the different gcd
strata.

---

# 31. One sequence and a Fourier formulation of the quadratic equations

There is a useful uniform formula that includes the exceptional entries.
For any odd \(n\), choose \(b_g\) with
\[
 b_0=-\delta^{-1/2},\qquad |b_g|=1\ (g\ne0),\qquad
 b_{-g}=\overline{b_g}.
\]
For a phase solution, take \(b_g=z_g^{-1}\) for \(g\ne0\).
Put
\[
 \lambda=\frac{\sqrt\delta}{\delta-1},\qquad
 \mu=1-\delta^{-1}.
\]
Then the whole matrix is
\[
 \boxed{
 A_{g,h}=\lambda b_gb_{h-g}b_{-h}
            +\mu\,\mathbf1_{g=0}\mathbf1_{h=0}.
 }
 \tag{31.1}
\]
Exactly one zero index gives \(-1/(\delta-1)\). At \((0,0)\), the
right-hand side is
\(-1/(\delta(\delta-1))+1-1/\delta=(\delta-2)/(\delta-1)\).
Rotation and Hermitian symmetry follow directly from the three factors.
Also
\[
 \sum_g|b_g|^2=n-1+1/\delta=\delta-1.
\]

For \(h\ne0\), let
\[
 f_h(m)=b_mb_{h-m}=b_m\overline{b_{m-h}},\qquad
 \widehat f_h(k)=\sum_{m=0}^{n-1}f_h(m)e^{-2\pi i km/n}.
\]
The quadratic Izumi equation becomes
\[
 \lambda^2\sum_m f_h(m+g)\overline{f_h(m)}=\mathbf1_{g=0}.
\]
Taking the discrete Fourier transform in \(g\) proves the equivalence
\[
 \boxed{
 |\widehat f_h(k)|^2=\frac{(\delta-1)^2}{\delta}
 \quad(h\ne0,\ k\in\mathbb Z_n).
 }
 \tag{Q}
\]
The entire \(h=0\) quadratic system holds automatically for the
exceptional column, using \(\delta^2=n\delta+1\).

Equivalently, the unit vector \(v=b/\sqrt{\delta-1}\) has a prescribed
discrete ambiguity function:
\[
 \left|\sum_m v_m\overline{v_{m-h}}e^{-2\pi i km/n}\right|^2
 =\begin{cases}
 1,&(h,k)=(0,0),\\
 \delta^{-2},&h=0,\ k\ne0,\\
 \delta^{-1},&h\ne0.
 \end{cases}
 \tag{31.2}
\]
The \(h=0,k\ne0\) overlap itself is \(-1/\delta\). This formulation
provides a concrete target for a character-sum or special-function
identity. The two nontrivial magnitudes differ, so this is not the
usual equal-overlap SIC condition.

Under the Stark construction, the natural phase target is
\[
 b_g^4=s_g\quad(g\ne0),
\]
with coherent root choices and the prescribed \(b_0\). Formula (31.1)
then gives (28.1) immediately. If a phase reconstruction initially
gives \(b_g^4=s_g\chi(g)\) for an additive character \(\chi\), its
unique fourth-root character removes \(\chi\) without changing the
generic entries, since \(n\) is odd.

**Remaining equation.** Let \(\mathcal A_{g,h}(b)\) denote the explicit
right-hand side of (31.1). Besides (Q), one must prove
\[
 \sum_m\mathcal A_{m,g+h}(b)
   \overline{\mathcal A_{m+k,g}(b)\mathcal A_{m+l,h}(b)}
 =\mathcal A_{g+l,k}(b)\mathcal A_{h+k,l}(b)
  -\delta^{-1}\mathbf1_{g=0}\mathbf1_{h=0}
 \tag{C}
\]
for all indices. Away from the explicit exceptional terms this is a
six-factor finite-sum identity in \(b\).
No implication from (Q) to (C) is proved here. They are verified
independently in Section 29. Neither the multiplicative cocycle law
nor Stark algebraicity by itself proves these additive identities.

[`hi_phase_reductions.py`](hi_phase_reductions.py) checks the rational
cocycle identities and binary sign ranks exactly, checks the Fourier
equivalence on arbitrary phases as well as a solution, and verifies
(Q) for the recorded \(n=13\) phases at 80-digit precision. Its
numerical checks supplement the derivation; the independent GP
certificates supply the finite existence proofs.

---

# 32. An unconditional infinite family of arithmetic inputs over one field

Restricting an infinitude strategy to primes \(p\) with
\(h(\mathbb Q(\sqrt{p^2+4}))=1\) would introduce a separate unproved
infinitude requirement. There is an explicit alternative if the target
is infinitely many **odd orders**, as in the present question.

Let
\[
 K=\mathbb Q(\sqrt5),\qquad \epsilon=(1+\sqrt5)/2,
 \qquad m>1,\quad m\equiv1,5\pmod6,
\]
and set
\[
 \delta_m=\epsilon^m,\qquad n_m=L_m=\epsilon^m-\epsilon^{-m}.
\]
Here \(L_m\) is the usual Lucas number for odd \(m\), and \(F_m\)
below is the Fibonacci number. Then
\[
 \delta_m^2-n_m\delta_m-1=0,\qquad
 n_m^2+4=5F_m^2.
\]
These give infinitely many distinct odd \(n_m\), all with \(K_{n_m}=K\).
No assertion that infinitely many of them are prime is needed.

## 32.1 Exact ray group and exact unit index

**Proposition.** Put \(\mathfrak a_m=(\epsilon^m-1)\). Then
\[
 \mathcal O_K/\mathfrak a_m\simeq\mathbb Z/n_m\mathbb Z,
\]
and the residue of \(\epsilon\) has exact order \(m\). Consequently
\[
 \boxed{
 \operatorname{Cl}_{\mathfrak a_m\infty_+}(K)
 \simeq(\mathbb Z/n_m\mathbb Z)^\times/\langle\bar\epsilon\rangle,
 \qquad
 [K^{\mathfrak a_m\infty_+}:K]=\frac{\varphi(n_m)}m.
 }
 \tag{32.1}
\]

**Proof.** The expansion
\(\epsilon^m=F_m\epsilon+F_{m-1}\) and the identity
\(n_m^2-5F_m^2=-4\) show \(\gcd(F_m,n_m)=1\), because \(n_m\)
is odd. Hence in the quotient
\[
 \bar\epsilon=(1-F_{m-1})F_m^{-1}\pmod{n_m}.
\]
The quotient has size \(|N(\epsilon^m-1)|=n_m\), proving the ring
isomorphism. Its unit order divides \(m\). If
\(0<r<m\) and \(\epsilon^r\equiv1\pmod{\mathfrak a_m}\), then
\(n_m\) divides \(N(\epsilon^r-1)\). For odd \(r\) this norm is
\(-L_r\); for even \(r\) it is \(2-L_r\). Its absolute value is
nonzero and strictly less than \(n_m\), a contradiction.

The field \(K\) has class number one: its Minkowski bound is
\(\sqrt5/2<2\). Its units are generated by \(-1\) and \(\epsilon\).
In the one-infinite-place ray exact sequence, \(-1\) removes the
sign factor and the remaining positive-unit image is generated by
\(\bar\epsilon\). This proves (32.1). ∎

The examples are reproduced by [`hi_pell_ray.gp`](hi_pell_ray.gp), with
results in [`hi_pell_ray_results.txt`](hi_pell_ray_results.txt).

| \(m\) | \(n_m\) | ray group | ray degree |
|---:|---:|---|---:|
| 5 | 11 | \(C_2\) | 2 |
| 7 | 29 | \(C_4\) | 4 |
| 11 | 199 | \(C_{18}\) | 18 |
| 13 | 521 | \(C_{40}\) | 40 |
| 17 | 3571 | \(C_{210}\) | 210 |
| 19 | 9349 | \(C_{492}\) | 492 |
| 23 | \(64079=139\cdot461\) | \(C_{1380}\times C_2\) | 2760 |
| 25 | \(167761=11\cdot101\cdot151\) | \(C_{300}\times C_{10}\times C_2\) | 6000 |

Only \(n=11,29\) in this table have the new HI certificates of
Section 29. The later rows are arithmetic computations, not claimed
categorifications.

## 32.2 A fixed maximal-order RM point and explicit characteristics

There is a necessary correction when specializing the analytic route
to this family:
\[
 [\mathcal O_K:\mathbb Z[\delta_m]]=F_m.
\]
Thus the lattice \(\mathbb Z+\mathbb Z(-\delta_m)\) used naively in
Section 23 is a nonmaximal order. It cannot silently be identified
with the maximal-order ray problem in (32.1).

Instead, use the fixed element \(\beta=-\epsilon\), viewed under the
nonphysical real embedding, so numerically
\(\beta=(\sqrt5-1)/2>0\). Its lattice
\(\mathbb Z+\mathbb Z\beta\) is \(\mathcal O_K\). Put
\[
 M_0=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad M_m=M_0^m,
 \qquad
 \mathbf r_{m,u}=-\frac{u}{n_m}
 \binom{F_{m-1}+1}{F_m}.
 \tag{32.2}
\]
Then, exactly,
\[
 M_m\beta=\beta,\qquad j_{M_m}(\beta)=\delta_m^{-2}>1
 \quad\text{at the chosen embedding}.
\]
For odd \(m\), the Fibonacci identities give
\[
 M_m-I=n_m
 \begin{pmatrix}F_{m-1}&F_m\\F_m&F_{m+1}\end{pmatrix},
\]
so \(M_m\equiv I\pmod{n_m}\) and it stabilizes every displayed
characteristic. In the convention
\([[\mathbf r,\beta]]=r_2\beta-r_1\),
\[
 [[\mathbf r_{m,u},\beta]]
 =\frac{u(1+\delta_m)}{n_m}
 =\frac{u\delta_m}{\delta_m-1}.
\]
For \(u\) coprime to \(n_m\), its denominator ideal is precisely
\(\mathfrak a_m\). With the totally positive generator
\(\alpha=\delta_m(\delta_m-1)\), the numerator becomes
\[
 \alpha[[\mathbf r_{m,u},\beta]]=u\delta_m^2
 \equiv u\pmod{\mathfrak a_m}.
\]
This realizes the desired residue labels at **one fixed RM point**,
with stabilizer matrices that are powers of a single matrix.
It uses the RM/ray correspondence of
[Kopp, Sections 3 and 8](https://arxiv.org/html/2411.06763v2), but
the displayed specialization is derived here. This section does not
assert that the multiplier normalization from the \(p=17\) case
carries over unchanged.

When \(n_m\) is composite, the full HI matrix also needs nonunit
residue labels. These require the ray class monoid and values for
smaller conductors, as in Kopp's Proposition 6.11; the invertible ray
orbit alone supplies too few labels. The prime-only sign algorithm
also needs an extension to the gcd strata.

The subsequence \(m=5^k\), \(k\ge1\), even gives nested moduli,
since \(\epsilon^a-1\) divides \(\epsilon^{ab}-1\). It is therefore
a possible setting for a distribution argument. A distribution law
for units would still need a proof that it preserves (Q) and (C)
as the additive group changes size.

---

# 33. What an infinitude proof now needs

This records the target after the first continuation. Sections 34–37
sharpen it to one balanced identity and extend the sign theorem.

The work above proves finite existence and removes two general
obstacles: recovering higher ratio types and managing the numerous
root signs in prime order. It does not prove existence for infinitely
many \(n\).

A precise sufficient target is now available. For infinitely many
\(m\equiv1,5\pmod6\), construct physical phases \(b_g\),
\(g\in\mathbb Z_{L_m}\), with
\[
 b_0=-\delta_m^{-1/2},\qquad b_{-g}=\overline{b_g},\qquad
 |b_g|=1\ (g\ne0),
\]
and prove **(Q) and (C)** of Section 31. Formula (31.1) and the
Izumi construction then give the desired infinite family.

The candidate is to take coherent fourth roots of ray/monoid Stark
values at the explicit parameters (32.2). A proof through this
candidate must establish the following substantive points:

1. Define and normalize values for all required residues, including
   nonunits at composite \(L_m\), and produce the physical phases.
   If using the algebraic route, prove the necessary fourth-root lifts
   and sign compatibility; algebraicity of the Stark units alone is
   weaker than these requirements.
2. Prove the finite Fourier identity (Q) for those phases, uniformly
   in the chosen exponents \(m\).
3. Prove the cubic finite-sum identity (C), or prove a theorem that
   makes it follow from the particular construction and (Q).

These requirements are not supplied by the multiplicative
\(2-\operatorname{Frob}_{(2)}\) law, the usual Stark conjecture, or
class-field existence. They are the remaining analytic/algebraic
existence problem. In an analytic construction that directly produces
the physical phases and proves the two identities, prior Stark
algebraicity would not be necessary for existence.

The suggested next experiment, \(n=199\), is now complete in
Section 35.3. It stays over \(\mathbb Q(\sqrt5)\) with ray degree
18. The beta reduction and exact integer batches made its full cubic
verification feasible. This tests the fixed-field formula at a larger
order; an infinitude theorem still requires a uniform construction.


---

# 34. One balanced finite beta identity encodes the entire system

There is a uniform reduction beyond Section 31: **within its phase
ansatz, (Q) and (C) together are equivalent to a single balanced finite
beta identity**. This is an algebraic change of formulation, proved
below; it does not assert that arbitrary Stark values satisfy the identity.
It applies to every odd order, including composite orders.

Write \(d=\delta\), \(d^2=nd+1\), and retain
\[
 b_0=-d^{-1/2},\quad b_{-u}=\overline{b_u},\quad
 |b_u|=1\quad(u\ne0),\qquad
 \lambda=\frac{\sqrt d}{d-1},\quad \mu=\frac{d-1}{d}.
\]
All indices below lie in \(\mathbb Z_n\). For two triples
\(\mathbf a=(a_1,a_2,a_3)\), \(\mathbf c=(c_1,c_2,c_3)\)
satisfying \(\sum_i a_i+\sum_j c_j=0\), define
\[
 S(\mathbf a,\mathbf c)
 =\sum_m\prod_{i=1}^3 b_{m+a_i}\prod_{j=1}^3 b_{-m+c_j},
 \qquad
 P(\mathbf a,\mathbf c)=\prod_{i,j=1}^3 b_{a_i+c_j}.
\]
Put \(q=d^{-1}\), \([r]_q!=\prod_{s=1}^r(1+q+\cdots+q^{s-1})\),
and let \(m_x\) be the multiplicity of \(x\) in \(\mathbf a\).
The identity is
\[
 \boxed{\quad
 S(\mathbf a,\mathbf c)=\lambda^{-1}P(\mathbf a,\mathbf c)
 +\frac{(d-1)^3}{d^2}\,
  \mathbf1_{\{c_1,c_2,c_3\}=\{-a_1,-a_2,-a_3\}}
  \prod_x[m_x]_{1/d}! .\quad} \tag{34.1}
\]
The braces in the indicator denote **multisets**. Repeated entries
matter: the three possible correction factors are
\[
 1,\qquad 1+d^{-1},\qquad
 (1+d^{-1})(1+d^{-1}+d^{-2}),
\]
for multiplicities \(1+1+1\), \(2+1\), and \(3\), respectively.

A matrix in the exact certificates really has the required physical
phase form. To see this without numerical phase recognition, let
\(r_h=B_{1,h}/\sqrt d\), \(2\le h<n\), put \(z_0=z_1=1\),
and set \(z_h=\prod_{t=2}^h r_t\). The exact row norms give
\(|z_h|=1\), and the mirror row identity gives
\(z_gz_{n-g}=z_{n-1}\) for \(g\ne0\). Choose any unit-modulus
\(u\) with \(u^n=z_{n-1}\), and put \(b_g=u^g/z_g\) for
\(g\ne0\), with the prescribed exceptional \(b_0\).
Then \(b_{-g}=\overline{b_g}\). The checked prefix-product formula
for the upper triangle gives
\(B_{g,h}=\sqrt d\,b_gb_{h-g}b_{-h}\); Hermitian symmetry gives
the lower triangle. The exceptional entries supply (31.1) everywhere.
The choice of \(u\) changes the sequence only by a cyclic character.

## 34.1 Change of variables for the interior cubic equations

For \((g,h,k,l)\), set
\[
 \mathbf a=(0,k-g,l-h),\qquad
 \mathbf c=(g+h,-k,-l). \tag{34.2}
\]
Their cross-sum matrix is
\[
 (a_i+c_j)=
 \begin{pmatrix}
 g+h&-k&-l\\
 h+k&-g&k-g-l\\
 g+l&l-h-k&-h
 \end{pmatrix}. \tag{34.3}
\]
Conversely, shift \(a_i\mapsto a_i-a_1\),
\(c_j\mapsto c_j+a_1\), then set
\(k=-c_2\), \(l=-c_3\), \(g=-c_2-a_2\),
\(h=-c_3-a_3\). Thus (34.2) parametrizes every balanced pair,
up to a harmless reindexing of the sum.

If \(g,h,g+h\ne0\), substitute
\(A_{u,v}=\lambda b_u b_{v-u}b_{-v}+\mu\mathbf1_{u=v=0}\)
into (C). The three factors on its left have no origin correction.
After dividing its residual by
\(\lambda^3b_{-(g+h)}b_gb_h\), the result is precisely the
residual of (34.1).

Indeed, the two generic factors on its right give
\(\lambda^{-1}P\). An origin correction on the right occurs
only at \((k,l)=(0,-g)\) or \((-h,0)\). Each contributes
\(\mu/\lambda^2=(d-1)^3/d^2\) after division. These are
exactly the possible multiset matches when \(g,h,g+h\ne0\);
then all three entries of \(\mathbf a\) are distinct. To see the
last assertion directly, a matching permutation must avoid the three
nonzero cross entries corresponding to \(g,h,g+h\). Its only
possibilities are the two derangements. A repeated entry would give
a forbidden matching permutation as well.

In particular, when **all nine cross sums are nonzero**, the remaining
cubic equation has the simple form
\[
 \sum_m\prod_i b_{m+a_i}\prod_j b_{-m+c_j}
 =\frac{d-1}{\sqrt d}\prod_{i,j}b_{a_i+c_j}. \tag{34.4}
\]

## 34.2 Every collision case follows from (Q)

For a full multiset match, the three sums and product terms in (34.1)
are determined by norms alone. They are as follows.

| Multiplicity in \(\mathbf a\) | \(S\) | \(\lambda^{-1}P\) |
|---|---|---|
| \(1+1+1\) | \(n-3+3/d\) | \(-(d-1)/d^2\) |
| \(2+1\) | \(n-2+d^{-1}+d^{-2}\) | \(-(d-1)/d^3\) |
| \(3\) | \(n-1+d^{-3}\) | \(-(d-1)/d^5\) |

Subtracting the last column and using \(n=d-d^{-1}\) gives exactly
the three correction coefficients in (34.1).

For a collision without a full multiset match, permute the triples
so that \(a_1+c_1=0\). The corresponding pair of factors in the
summand is
\[
 b_{m+a_1}b_{-m-a_1}
 =1+(d^{-1}-1)\mathbf1_{m=-a_1}.
\]
The unrestricted sum of the other four factors is a quadratic
correlation. In fact, set \(H=a_2+c_2\), \(V=a_3+c_2\).
The balancing condition identifies that sum with
\[
 \sum_t b_t b_{H-t}b_{-t-V}b_{t+V-H}. \tag{34.5}
\]
This is exactly a correlation from (Q). Both relevant shifts are nonzero: if either
\(H\) or \(V\) vanishes, the remaining two pairs match, contrary
to the assumption. Hence (34.5) vanishes by (Q).

For clarity, one can instead normalize \(a_2=0\) and write the
remaining two triples as \((0,V-H)\) and \((H,-V)\).
Their four-factor sum is
\(\sum_t b_t b_{t+V-H}b_{-t+H}b_{-t-V}\),
which is exactly (34.5).
The surviving term of \(S\) is therefore
\[
 (d^{-1}-1)
 \prod_{i=2}^3b_{a_i-a_1}\prod_{j=2}^3b_{c_j+a_1}.
\]
The product \(P\) is \(b_0\) times these four boundary factors,
since its other four factors pair to
\(|b_H|^2|b_V|^2=1\). Finally
\(\lambda^{-1}b_0=d^{-1}-1\), proving (34.1) in this case.

Conversely, (34.1) implies every nontrivial quadratic correlation.
Given nonzero \(g,h\), take
\[
 \mathbf a=(t,0,g-h),\qquad \mathbf c=(-t,h,-g).
\]
There is a cross-zero pair but no full multiset match. The calculation
just made subtracts the exceptional term from (34.1) and leaves
\(\sum_m b_m b_{h-m}b_{-m-g}b_{m+g-h}=0\).
The zero-shift correlations follow from the norms and
\(d^2=nd+1\), and the \(h=0\) column of (Q) is automatic.
Thus the collision part of (34.1) recovers all of (Q).

## 34.3 The boundary cubic equations also follow from (Q)

Here are explicit reductions, including the exceptional origin.
Write \(c_0=(d-1)^{-1}\), so \(A_{u,0}=\mathbf1_{u=0}-c_0\).
For \(g=0\), \(h\ne0\), the left side of (C), using (Q), becomes
\[
 A_{-k,h}\overline{A_{l-k,h}}-c_0\mathbf1_{l=0}.
\]
For \(l\ne0\) this equals \(A_{l,k}A_{h+k,l}\) directly from
the phase formula and the unit norms at nonzero indices. For \(l=0\),
use \(|A_{u,h}|^2=\lambda^2\) when \(u\ne0,h\), and
\(|A_{u,h}|^2=c_0^2\) otherwise. The case \(h=0,g\ne0\)
follows by exchanging \((g,k)\) with \((h,l)\).

For \(h=-g\ne0\), the left side similarly reduces to
\[
 \overline{A_{k,g}}A_{-l,g}-c_0\mathbf1_{k=g+l}.
\]
If \(k\ne g+l\), the phase products equal the right side of (C).
If \(k=g+l\), the assertion reduces to the same two norm values;
use \(\lambda^2-c_0=c_0^2\).

For \(g=h=0\), the left side is
\[
 \mathbf1_{k=l=0}
 -c_0(\mathbf1_{k=0}+\mathbf1_{l=0}+\mathbf1_{k=l})
 +3c_0^2-nc_0^3.
\]
The right side is \(|A_{l,k}|^2-d^{-1}\). The cases
\(k=l=0\), exactly one of \(k=0,l=0,k=l\), and none of them
agree by \(d^2=nd+1\).

Combining these observations proves the equivalences
\[
 \boxed{\quad
 (Q)+(C)\quad\Longleftrightarrow\quad(34.1)
 \quad\Longleftrightarrow\quad(Q)+(34.4)
 \text{ for all cross-zero-free balanced pairs}.\quad}
\]
No implication from (Q) alone to (C) in arbitrary order is proved here.

## 34.4 Symmetry and exact verification

The two sides of (34.1) are invariant under independent permutations
of the triples, interchange of the triples, and opposite translation
of the triples. The first two operations form
\((S_3\times S_3)\rtimes C_2\), of order 72. For prime order,
checked multiplier covariance supplies the scalar action as well.
It is enough to check (C) at one representative of each resulting
orbit of cross-zero-free quadruples; all other equations follow by
the preceding proof. Scalar covariance also reduces (Q) to the
columns \(h=0,1\).

| Prime | Earlier cubic scalar representatives | New beta representatives |
|---|---:|---:|
| 7 | 401 | 6 |
| 11 | 1,465 | 17 |
| 13 | 2,381 | 30 |
| 17 | 5,221 | 63 |
| 19 | 7,241 | 91 |
| 29 | 25,261 | 320 |
| 199 | 7,920,401 | 108,406 |

At \(n=199\), this changes the cubic summand count from
1,576,159,799 to 21,572,794. These are exact enumeration counts,
not estimates of runtime. It remains a substantial computation.

`hi_beta_reductions.py` independently checks the orbit coverage,
the rational collision coefficients, the change of variables on
arbitrary nonsolutions at orders 3, 5, 7, 9, and every balanced
identity for the recorded order-13 solution. `hi_stark_seedless.gp`
uses the same proven reduction for exact number-field certificates.
The optional `HI_STARK_FULL_CUBIC=1` runs the older exhaustive scalar
check and the full quadratic check too; both methods agree exactly
at orders 7, 11, 13, 17, 29.


---

# 35. Exact ideal evidence and the next finite orders

## 35.1 Quadratic equations imply cubic equations at orders 3, 5, 7, 9

There is now an exact algebraic result supporting the possible
redundancy of (C), beyond the earlier numerical experiments. Put
\(c_g=\sqrt d\,b_g\), so that \(c_0=-1\) and
\(c_gc_{-g}=d\) for \(g\ne0\). Over
\(K=\mathbb Q(d)\), \(d^2=nd+1\), consider the ideal
\[
 I_n=\left(
 c_gc_{-g}-d,\quad
 \sum_m c_m c_{h-m}c_{-m-g}c_{m+g-h}
 \ \bigm|\ g,h\ne0\right)
 \subset K[c_1,\ldots,c_{n-1}]. \tag{35.1}
\]
The second set of generators is precisely the nontrivial part of (Q)
in these coordinates. For each balanced cross-zero-free pair, set
\[
 F_{\mathbf a,\mathbf c}
 =d^2\sum_m\prod_i c_{m+a_i}\prod_j c_{-m+c_j}
 -(d-1)\prod_{i,j}c_{a_i+c_j}. \tag{35.2}
\]
Here the bold \(\mathbf c\) denotes the second triple of indices,
whereas \(c_g\) denotes a variable. The different degrees, six and
nine, are intentional: clearing the phase normalization multiplies
(34.4) by \(d^5\).

`hi_quadratic_ideal.py` computes a reduced Gröbner basis in Singular
and verifies the actual ideal memberships
\[
 \boxed{F_{\mathbf a,\mathbf c}\in I_n\quad
 \text{for all such pairs when }n=3,5,7,9.}
\]
The ideal is invariant under scalar permutations of its variables.
Together with the exact beta symmetries, this makes the finite
representative checks exhaustive even without assuming Galois
covariance of an individual solution. Section 34 then proves
\((Q)\Rightarrow(C)\) for every phase solution at these four orders.
This is ideal membership, stronger than numerical vanishing or
membership merely in the radical.

| \(n\) | Reduced Gröbner basis size | \(\dim_K K[c_1,\ldots,c_{n-1}]/I_n\) | Beta representatives tested |
|---|---:|---:|---:|
| 3 | 3 | 6 | 1 |
| 5 | 14 | 20 | 2 |
| 7 | 41 | 42 | 6 |
| 9 | 132 | 108 | 14 |

The dimensions in this table count scheme length; reducedness or a
classification of physical solutions is not inferred from these
numbers. The same direct Gröbner computations at orders 11 and 13
reached a 300-second limit without completing. They establish no
implication at those orders. A **uniform proof of (35.2) lying in
(35.1)** would remove (C) as a separate requirement in the phase
ansatz. Existence of physical solutions of (Q) would still need proof.

## 35.2 The order-19 certificate is now complete

The earlier partial checkpoint in Section 29.4 has been completed.
The construction from the full ray Stark polynomial gives exact
fourth-root lifts, sign transport, every instance of (Q), all norm,
rotation and multiplier identities, and all of (C), the last by
91 balanced-beta representatives. The field has absolute degree 72
and ray group \(C_{18}\times C_2\).

Two further exact assertions identify the formerly recognized data.
If \(E_{19}\) is the degree-36 polynomial of Section 26, the matrix
satisfies
\[
 E_{19}(-B_{1,2}^2/d)=0.
\]
Its principal-orbit coefficient
\[
 \tau=\sum_{g=1}^{18} B_{g,2g}^2/d
\]
satisfies
\[
 \tau^2-(-333455+17502d)\tau+61207710-3212584d=0.
\]
These checks occur **after** the construction and use no numerical
HI seeds. The earlier exact irreducibility and Hilbert-class-field
computations therefore identify the full relative minimal polynomial
and its two branch factors without a phase-recognition assumption.
The other Hilbert-class conjugate of the matrix also satisfies every
equation: the ray Galois group is abelian, so its action commutes with
the verified physical conjugation and fixes \(d\).

The logs `hi_stark19_results.txt` record the exact initial field and
root stages, the completed matrix verification, and these downstream
polynomial assertions. The old partial log is retained as history.

## 35.3 The fixed-field experiment at order 199

For \(n=L_{11}=199\), the base field is \(\mathbb Q(\sqrt5)\),
the ray group is \(C_{18}\), and the absolute field degree is 36.
The exact construction has passed all field and physical-involution
checks, every fourth-root lift, sign transport of rank 98, every
quadratic equation, rotation, scalar covariance, and all generic
norms and fourth-power Stark identities. In particular, the
fixed-field candidate satisfies the complete Fourier identity (Q)
at this much larger order.

**All 108,406 cubic representatives have now passed exactly**, in
16 disjoint batches. Together with the preceding checks, this is a
complete existence certificate at order 199. The construction and
coverage logs are `hi_stark199_construction_results.txt` and
`hi_stark199_cubic_results.txt`.

The saved `hi_stark199_certificate.gp` contains 458 distinct entries
and their index matrix, plus the defining field and involutions.
`hi_stark19_certificate.gp` has the analogous data with 62 distinct
entries. These are exact rational expressions, with no phase seeds.
`hi_stark_verify_certificate.py` verifies the fields, physical
involutions, coherent phase form, symmetries and quadratic equations
directly from the saved data, then runs the cubic batches. For example:

```sh
python hi_stark_verify_certificate.py hi_stark199_certificate.gp --jobs 16
```

The `--structure-only` option stops before the separately required
cubic stage. It does not report a complete existence certificate.

The separate final-stage verifier `hi_stark_cubic_batches.py` clears
a common denominator \(D\) of \(B\) and \(d\). With
\(X=DB\) and \(Y=D(d-1)\), it checks the integer-polynomial
congruences
\[
 \sum_jX_{j,g+h}X_{g,j+k}X_{h,j+l}
 =Y X_{g+l,k}X_{h+k,l}\pmod{P}, \tag{35.3}
\]
where \(P\) is the monic absolute defining polynomial. Hermitian
symmetry converts conjugation to transposition. The representatives
are cross-zero-free, so the exceptional \(g=h=0\) term is absent.
All operations take place in \(\mathbb Z[y]/(P)\); there is no
floating-point tolerance or probabilistic modular test. Disjoint
batches together cover every representative, and the log records
the SHA-256 of the matrix checkpoint to identify their common input.
The previously completed field, phase-form, covariance and quadratic
checks remain essential parts of this certificate.

---

# 36. Sign descent at composite orders and a prime-power theorem

The prime-order sign argument extends to a useful general criterion.
Let \(G\) be a finite abelian group of odd order and let a finite
group \(H\) act on \(G\) and on the coefficient field. Write
\(\sigma_h\) for the field action. Assume a normalized symmetric
phase cocycle \(C\) has been constructed and that its covariance
errors
\[
 E_h(a,b)=\frac{\sigma_h(C(a,b))}{C(ha,hb)}
\]
lie in \(\{\pm1\}\). The fourth-power identities and the real
embedding argument of Section 30 give this hypothesis in the prime
construction; it must be checked for a proposed composite
construction. Also assume \(-1\in H\) acts as physical conjugation,
so \(E_{-1}=1\).

Define
\[
 f_h(a)=E_h(a/2,a/2).
\]
The normalized sign-valued cocycle calculation gives, uniquely,
\[
 E_h(a,b)=\frac{f_h(a)f_h(b)}{f_h(a+b)},\qquad
 f_{hk}(a)=f_h(ka)f_k(a). \tag{36.1}
\]
Uniqueness uses the absence of nontrivial homomorphisms
\(G\to\{\pm1\}\). For \(a\in G\), let
\(H_a=\{h:ha=a\}\). Then
\[
 \chi_a:H_a\longrightarrow\{\pm1\},\qquad
 \chi_a(h)=f_h(a),
\]
is a character.

**Sign descent criterion.** A correction
\(C'(a,b)=C(a,b)t_at_b/t_{a+b}\), \(t_0=1\),
\(t_a\in\{\pm1\}\), with exact \(H\)-covariance exists if
and only if every \(\chi_a\) is trivial. When it exists, the
remaining freedom is one sign per nonzero \(H\)-orbit in \(G\).
The correction respects \(t_{-a}=t_a\).

To prove the criterion, exact covariance is equivalent, by uniqueness
in (36.1), to
\[
 t_{ha}=f_h(a)t_a. \tag{36.2}
\]
For \(h\in H_a\) this requires \(\chi_a(h)=1\). Conversely,
choose one sign at a representative of each orbit and extend by
(36.2). The cocycle identity makes this well-defined precisely when
the stabilizer characters vanish. Finally \(f_{-1}=1\) gives the
negation condition. Two choices differ by an orbit-constant sign
function. Distinct such functions give distinct corrected cocycles,
because their quotient cannot be a nontrivial sign character of the
odd group \(G\).

**Prime-power corollary.** For
\(G=\mathbb Z_{p^k}\), \(p\) odd, and
\(H=(\mathbb Z/p^k)^\times\), all stabilizers of nonzero
elements have odd order. An element of additive order \(p^j\)
has stabilizer of order \(p^{k-j}\), the kernel of reduction to
\((\mathbb Z/p^j)^\times\). Thus every stabilizer character is
trivial, and the sign correction always exists under the stated
phase and covariance-error hypotheses. There are exactly \(k\)
remaining orbit signs, one for each additive order
\(p,p^2,\ldots,p^k\), giving \(2^k\) choices before imposing (Q).
This removes a sign obstruction uniformly on an infinite family of
candidate orders. It does not supply their fourth-root lifts or (Q).

For general odd cyclic \(n\), the number of nonzero scalar orbits
is \(\tau(n)-1\), but their stabilizers can have even order. Their
characters cannot simply be ignored. The script
`hi_composite_signs.py` checks the prime-power orbit counts and
constructs an abstract example at \(n=15\) with
\(f_{-1}=1\), yet \(\chi_3(11)=-1\). This is an example of
sign-error data, not a claimed HI or Stark counterexample.

There is a concrete class-field sufficient condition for general
\(n\). If \(a\) has additive order \(q\), require its diagonal
fourth-root lift \(B_{a/2,a}\) to lie in the field fixed by
\(\sigma_h\) for every \(h\equiv1\pmod q\). Then
\[
 f_h(a)=\sigma_h(B_{a/2,a})/B_{a/2,a}=1
 \quad(h\in H_a),
\]
and the obstruction vanishes. In a ray-monoid construction this is
the expected lower-conductor field condition on the **root lift**;
having only its fourth power in that field is insufficient. Once
these lower-conductor lifts and the global phase cocycle are
constructed, there is no further composite sign compatibility
problem beyond the orbit signs.

---

# 37. The sharpened infinitude target

The strongest uniform target from this continuation is now explicit:
construct, for infinitely many odd orders, the physical sequence of
Section 34 and prove **the single balanced identity (34.1)**. That
identity includes unitarity through its collision cases and gives the
remaining Izumi equations through its cross-zero-free cases. This
would be an existence proof without needing prior Stark algebraicity.

There are two concrete arithmetic settings. The fixed-field Lucas
family of Section 32 supplies explicit RM characteristics and ray
moduli; its composite labels require lower-conductor root control as
in Sections 36 and 38. Alternatively, the orders \(p^k\) are already an
unconditional infinite sequence, and Section 36 makes sign descent
automatic once the phase/root hypotheses hold. For that route the
quadratic fields vary with \(k\), and the phase construction and
finite identities remain unproved. Neither setting requires an
unproved infinitude of special primes.

The beta reformulation suggests a more specific analytic comparison
than the general appeal to quantum dilogarithms. The integral
identity (1.11) in
[Bazhanov–Sergeev, *A distant descendant of the six-vertex model*](https://arxiv.org/html/2310.08427v2#S1.E11)
has three numerator and three denominator factors, a balancing
condition, and nine pairwise factors on the other side. The authors
relate it to the constant beta pentagon identity of Garoufalidis and
Kashaev. Our finite identity has a comparable pattern after using
\(b_{-x}=b_x^{-1}\) at nonzero indices. This comparison is a
research direction, not a specialization theorem.

A successful specialization would have to establish the finite
\(\mathbb Z_n\) sum, the normalization \((d-1)/\sqrt d\), and
all three collision coefficients in (34.1). The continuous integral
in that paper does not by itself provide them. The explicit fixed-RM
characteristics from Section 32 are candidates for such a descent;
no descent or limiting argument accomplishing it has been proved
here.

A second precise route is to prove the uniform ideal containment
(35.2) in (35.1), then construct physical solutions of (Q) uniformly.
The small-order containments and the larger exact Stark-derived
quadratic solutions support this approach, but they do not replace
those two required theorems. Existence for infinitely many \(n\)
remains open in these notes.


---

# 38. All fourth-root lifts collapse to one Kummer root

There is a stronger simplification of Sections 28, 30 and 36. The
many row-root computations can be replaced by **one fourth-root
condition**, followed by Galois transport and, at prime powers,
odd-degree norms. This does not assert the remaining sum identities.

## 38.1 An explicit inverse to the doubling-root map

Let \(L\) be the ray field, let \(\alpha=\sigma_2\) be its
residue-2 automorphism, and suppose \(\alpha(d)=d\). Then the two
root problems
\[
 D^4=d^2\frac{s^2}{\alpha(s)}
 \qquad\text{and}\qquad
 W^4=d^2s \tag{38.1}
\]
are equivalent **inside the same field \(L\)**. The mutually inverse
maps are
\[
 \boxed{\quad D=\frac{W^2}{\alpha(W)},\qquad
 W=\frac{d^2\alpha^{-2}(s)}
          {\alpha^{-2}(D)^2\alpha^{-1}(D)}.\quad} \tag{38.2}
\]
For example, raising the second expression to the fourth power and
using the first equation in (38.1) gives \(d^2s\); substituting it
into \(W^2/\alpha(W)\) returns \(D\) exactly. No extraction of
additional roots occurs in this inverse formula.

Thus even the single known doubling root \(B_{1,2}\) already gives
a fourth root of \(d^2s\). The apparently weaker doubling quotient
condition is not weaker at the level of fourth-root existence.
This is an algebraic equivalence, without any Stark conjecture.

For prime order, define \(W_a=\sigma_a(W)\) for \(a\ne0\).
At a physical embedding, \(\overline s=s^{-1}\) gives
\((W\overline W)^4=d^4\). Positivity of \(W\overline W\)
therefore forces \(W\overline W=d\). Consequently
\[
 b_0=-d^{-1/2},\qquad b_a=W_a/\sqrt d\quad(a\ne0)
\]
has the required physical norms and negation symmetry, and
\[
 \boxed{B_{g,h}=\frac{W_gW_{h-g}}{W_h}
 \quad(g,h,h-g\ne0).} \tag{38.3}
\]
The exceptional entries are prescribed as before. Every generic
fourth-power formula, rotation symmetry, Hermitian symmetry and
scalar covariance now follows directly. Since \(L\) has a real
embedding, a solvable fourth-root problem has exactly two roots in
\(L\); these give the two global generic sign choices. No separate
row-sign linear system is necessary for this construction.

The formula also recovers an already certified matrix, not just some
matrix with the same fourth powers. Write \(D_a=B_{a,2a}\). Then
\[
 W_a=\frac{d^2s_{a/4}}{D_{a/4}^{\,2}D_{a/2}},
 \qquad W_a^4=d^2s_a,\qquad W_a^2/W_{2a}=D_a.
\]
The quotient of the two normalized phase cocycles has values in
\(\{\pm1\}\) and trivial diagonal, hence is identically one by
the odd-order sign-cocycle lemma. Direct exact computation confirms
(38.3) for every generic entry of both saved matrices at orders
19 and 199. In this gauge the phase values themselves satisfy
\(b_a^4=s_a\); the cyclic-character ambiguity of the prefix-product
construction has been removed.

## 38.2 Odd-degree norm descent of the root

Let \(L/M\) have odd degree \(r\), with \(d\in M\), and suppose
\(N_{L/M}(s_L)=s_M\). If \(W_L^4=d^2s_L\), set
\[
 \boxed{\quad W_M=d^{(1-r)/2}N_{L/M}(W_L).\quad} \tag{38.4}
\]
Then
\[
 W_M^4=d^{2(1-r)}d^{2r}s_M=d^2s_M.
\]
If physical conjugation commutes with the norm and
\(W_L\overline W_L=d\), it also gives
\(W_M\overline W_M=d\). The exponent in (38.4) is an integer;
this is why odd degree removes the apparent extra root extraction.

For \(n=p^k\), \(p\) odd, write
\((d-1)=\mathfrak p^k\) in the maximal quadratic order. The prime
\(p\) splits since \(n^2+4\equiv4\pmod p\). The ray extensions
from conductor \(\mathfrak p^k\) to
\(\mathfrak p^j\), with the same infinite place, have degree a
power of \(p\). Thus (38.4) applies whenever the distinguished
units have the required norm compatibility. One top-level Kummer
root then supplies roots in every smaller nontrivial conductor.
There are initially up to \(2^k\) stratum signs in the phase ansatz.
Section 40 makes one necessary quadratic equation linear in transformed
signs; imposing the exact norm law leaves only a global sign.

## 38.3 Nonunit labels need their remaining numerator ideal

The lower-conductor values must be assigned to the correct ray-monoid
class. They cannot simply be copied from the identity class at the
smaller conductor. For \(g=p^j u\), \(p\nmid u\), cancelling
\(\mathfrak p^j\) from the numerator ideal gives
\[
 (g)\mathfrak p^{-j}=(u)\overline{\mathfrak p}^{\,j}.
\]
Therefore the label at additive order \(p^{k-j}\) includes the
Artin action of \(\overline{\mathfrak p}^{\,j}\). In compatible
normalizations, the intended formula is
\[
 s_{p^j u}
 =\sigma_u\sigma_{\overline{\mathfrak p}}^{\,j}
    (s_{k-j}),\qquad
 W_{p^j u}
 =\sigma_u\sigma_{\overline{\mathfrak p}}^{\,j}
    (W_{k-j}). \tag{38.5}
\]
Here \(s_{k-j}\) and \(W_{k-j}\) are the lower-conductor unit and
root obtained before applying that class label. The ideal calculation
is the specialization of the conductor-reduction formula in
[Kopp, Proposition 6.11, equation (6.35)](https://arxiv.org/html/2411.06763v2#S6.E35).
Its norm factor contributes no derivative correction because the
differenced zeta function vanishes at zero. The assertion identifying
canonical analytic values with algebraic Stark units remains subject
to the hypotheses stated in that proposition.

The need for this numerator ideal is visible at \(n=25\). Over
\(\mathbb Q(\sqrt{629})\), the ray groups at
\(\mathfrak p^2\) and \(\mathfrak p\) are \(C_{40}\) and
\(C_8\). The exact degree-five norm of the full Stark generator
is a root of the lower-conductor Stark polynomial. Its untwisted
cochain gives all quartic lifts and physical norms, but **none of its
four stratum-sign choices satisfies (Q)**. This rules out that
untwisted assignment; it does not rule out order-25 existence.

For the corrected assignment, the conjugate-prime Artin map can be
identified exactly without reducing a poorly conditioned power basis
at the ramified rational prime. An auxiliary prime above 23 has base
root \(d\equiv6\pmod{23}\), and its ray coordinate is 29 in
\(C_{40}\), while that of \(\overline{\mathfrak p}\) is 33.
The auxiliary Frobenius is identified modulo a squarefree factor of
\(P\bmod23\), and its \(33/29\bmod40\) power gives the desired
map. Its square is exactly the rational-2 Frobenius, as also follows
from the positive generator
\((d+1)/d\) of \(\overline{\mathfrak p}^{\,2}\), which is
congruent to 2 modulo \(\mathfrak p^2\).

## 38.4 A more economical sufficient target for prime powers

For a fixed odd prime \(p\), an infinitude proof along \(p^k\)
can now be organized around the following substantive assertions:

1. Construct compatible ray units with the physical involution and
   the same-support norm law across the nontrivial conductors.
2. Prove just **one** Kummer condition \(d_k^2s_k\in L_k^{\times4}\)
   at the top conductor. Equations (38.4)–(38.5) then produce all
   nonzero residue phases with their correct class labels.
3. Prove the balanced identity (34.1) for some choice of stratum
  signs, uniformly for infinitely many \(k\).

Section 40 replaces the sign search in the third item by a rational
linear system. If the roots are required to obey (38.4), only one
global sign remains, and one necessary quadratic equation uniquely
selects it whenever it can be selected at all.

The quadratic base field varies with \(k\). Class-field existence,
Stark algebraicity, and the norm formulas do not establish the last
two assertions. Nevertheless, this removes the separate collection
of mixed-index fourth-root problems and turns lower-conductor sign
compatibility into an explicit construction.


---

# 39. Complete exact existence at the composite order 25

The corrected construction of Section 38 passes **every** Izumi
equation at \(n=25\). It uses no numerical HI seed. The arithmetic
data are
\[
 K=\mathbb Q(\sqrt{629}),\quad h_K=2,\quad
 \operatorname{Gal}(L/K)=C_{40},\quad [L:\mathbb Q]=80,
\]
with lower ray group \(C_8\) and relative conductor-descent degree
five. One exact root \(W^4=d^2s\), its normalized norm
\(d^{-2}N(W)\), and the conjugate-prime Artin twist produce the
cochain on both nonzero residue strata. The untwisted assignment
fails (Q), while the corrected one passes it.

The independently verified coefficient artifact is
`hi_stark25_certificate.gp`, with SHA-256
```text
e19474b7d332a306ab2d13009d526a7bd484011bdbeeb7fa77eef7d10d73477b
```
It contains exact rational coefficients in a degree-80 number field.
The verifier checks the field and physical involution, every matrix
norm, the full coherent phase form, Hermitian and rotation symmetries,
scalar covariance, and all quadratic equations. For the last check,
the columns \(h=0,1,5\) cover all scalar strata.

The cubic enumeration for composite orders uses actual unit-group
orbits; it never normalizes an index by division by a nonunit.
There are 267,720 cross-zero-free quadruples and 246 representatives
under the balanced-beta symmetries. All 246 exact cubic checks pass
in eight disjoint batches. Section 34 covers every remaining cubic
equation. The complete log is `hi_stark25_verification_results.txt`.

To verify the saved artifact without rerunning Stark computations:
```sh
python hi_stark_verify_certificate.py hi_stark25_certificate.gp --jobs 8
```
To reproduce the construction in a fresh temporary directory:
```sh
hi_work=$(mktemp -d /tmp/hi25_reproduce.XXXXXX)
export HI_STARK_LIBRARY=1
export HI_STARK_CHECKPOINT="$hi_work/rows.bin"
export HI_SINGLE_ROW_CHECKPOINT="$HI_STARK_CHECKPOINT"
export HI_SINGLE_CONJUGATE_FROBENIUS="$hi_work/conjugate_prime.bin"
export HI_SINGLE_OUTPUT="$hi_work/certificate.gp"
gp -q -f hi_stark_seedless.gp hi_stark_prime_power.gp
gp -q -f hi_stark_seedless.gp hi_stark25_artin.gp
gp -q -f hi_stark_seedless.gp hi_stark_single_root.gp
python hi_stark_verify_certificate.py "$HI_SINGLE_OUTPUT" --jobs 8
```
The first three stages are construction stages; only the last command
certifies all equations. `hi_stark25_artin.gp` deliberately implements
the exact cyclic ray-group calculation for this order, without claiming
to handle every prime power. The single-root and sign formulas are
uniform. This is a finite existence theorem, not an induction step
from order 5 to order 25: the dimension and quadratic base field differ.


---

# 40. Prime-power sign selection becomes rational linear algebra

There is a further uniform reduction of the apparent \(2^k\) sign
search. Let \(n=p^k\), with \(p\) odd, and suppose a physical
cochain and its phase matrix \(B\) have already been constructed.
No quadratic or cubic equation is assumed. Changing the sign of
\(W_a\) on the valuation stratum \(v_p(a)=j\) multiplies it by
\(\epsilon_j\in\{\pm1\}\), for \(0\le j<k\).

## 40.1 One necessary quadratic equation is linear in new signs

Set
\[
 D=B_{1,2},\qquad T=D+\overline D,\qquad
 R_m=B_{m+1,1}B_{1,m}\quad(2\le m\le n-2).
\]
Partition the generic terms by
\(j=v_p(m^2-1)\), and define
\[
 C_0=1+\sum_{\substack{2\le m\le n-2\\p\nmid m^2-1}}R_m,
 \qquad
 C_j=\sum_{\substack{2\le m\le n-2\\v_p(m^2-1)=j}}R_m
 \quad(1\le j<k).
\]
The valuations in these sums are less than \(k\): the only square
roots of 1 modulo an odd prime power are \(\pm1\), and those
indices have been excluded. For the sign-changed matrix, the single
quadratic equation with \(g=h=1\) is exactly
\[
 \boxed{C_0-\epsilon_0T+
       \sum_{j=1}^{k-1}\epsilon_0\epsilon_jC_j=0.} \tag{40.1}
\]

Here is the sign calculation. The \(m=0\) term is 1. The two
terms at \(m=1,-1\) sum to \(-\epsilon_0T\). In every other
term, the cochain signs occur as
\(\epsilon_{v_p(m)}^2
  \epsilon_{v_p(m-1)}\epsilon_{v_p(m+1)}\).
If \(p\mid m\), both neighbors are units and this product is 1.
If \(m,m-1,m+1\) are all units it is again 1. Otherwise exactly
one neighbor has positive valuation \(j\), giving
\(\epsilon_0\epsilon_j\). Oddness of \(p\) is essential here.

The substitution
\[
 y_0=\epsilon_0,\qquad y_j=\epsilon_0\epsilon_j\ (j>0)
\]
is a bijection of the sign cube, with inverse
\(\epsilon_0=y_0\), \(\epsilon_j=y_0y_j\). Expanding (40.1)
in any rational basis of the coefficient field gives the exact
linear system
\[
 \boxed{\quad [-T\ C_1\ \cdots\ C_{k-1}]\,y=-C_0,
           \qquad y_j\in\{\pm1\}.\quad} \tag{40.2}
\]
If the \(k\) coefficient columns are rationally independent,
there is at most one sign choice even for this one necessary
equation. Solve the rational system and check that all coordinates
are signs. An inconsistent system, or a unique solution with a
coordinate other than \(\pm1\), rejects every stratum-sign choice
for the proposed roots. In deficient rank, intersect the rational
affine solution space with the sign cube before testing the other
quadratic equations.

For the saved order-25 matrix, the rational rank is exactly two and
the unique solution is \(y=(1,1)\). Directly testing the other
three stratum-sign choices independently confirms that **each fails
already at \(g=h=1\)**. The routine
`hi_prime_power_sign_candidates` implements (40.2); the one-root
constructor now uses it before the full quadratic check. Full rank
for all prime powers has not been proved, and this one equation
does not replace the remaining quadratic or cubic equations.

## 40.2 Exact norm compatibility leaves only a global sign

Under the norm hypotheses of Section 38, requiring the roots
themselves to satisfy (38.4) is stronger than independently choosing
a root on each stratum. If two compatible choices differ by signs
\(\eta_r\) at conductor level \(r\), an odd-degree norm gives
\(\eta_{r-1}=\eta_r^{[L_r:L_{r-1}]}=\eta_r\).
The Artin twists fix signs. Thus **all norm-compatible root choices
differ by one global sign**. This uses that the fields have a real
embedding, so their fourth roots of unity are only \(\pm1\).
It does not assert that every solution of (Q) must obey these norm laws.

Put \(U=C_0+\sum_{j>0}C_j\). For a global change
\(\epsilon_j=\eta\), equation (40.1) becomes
\[
 U=\eta T. \tag{40.3}
\]
For the Stark construction, \(T\ne0\) whenever \(s\ne1\).
Indeed, \(T=0\) and \(D\overline D=d\) would imply
\(D^2=-d\), hence \(D^4=d^2\). The doubling formula then gives
\(\alpha(s)=s^2\), where \(\alpha=\sigma_2\). If \(\alpha\)
has order \(r\), this forces \(s^{2^r-1}=1\). A field with a
real embedding has only the roots of unity \(\pm1\), so the odd
exponent forces \(s=1\), a contradiction.

Consequently the necessary and sufficient condition that one of
the two global choices satisfy this single quadratic equation is
\[
 U^2=T^2,
\]
and its sign is then determined algebraically by \(\eta=U/T\).
The selected cochain \((U/T)W\) is unchanged if the initially
extracted fourth root is replaced by its negative. There is no
remaining global choice after this equation is imposed.

The saved matrices at orders 19, 199 and 25 pass exact reconstruction
from the single root and the test \(U=T\ne0\). At order 25 the
reconstructed nonunit root is exactly
\(d^{-2}\sigma_{\overline{\mathfrak p}}N(W)\), with no additional
relative sign. `hi_single_root_checks.gp` reproduces these assertions;
`hi_prime_power_signs.py` separately checks (40.1) on arbitrary
phases and all sign choices at several prime powers.

The prime-power route to infinitude now has an explicit sign procedure.
What remains is a uniform source of the top Kummer root and a proof
of the balanced identity for the selected phases, or a construction
of physical quadratic solutions together with a uniform proof that
(Q) implies (C). Neither finite rank tests nor norm compatibility
establish those missing statements.


---

## Files from this exploration

- `hi_stark_seedless.gp` and `hi_stark_seedless_results.txt`  
  Construction without HI seeds and exact complete Izumi certificates
  for \(n=7,11,13,17,29\), including exact identification of the earlier
  \(n=13,17\) polynomials.

- `hi_stark19_certificate.gp`, `hi_stark25_certificate.gp`,
  `hi_stark199_certificate.gp`, and
  `hi_stark_verify_certificate.py`  
  Saved exact matrix data and an independent existence verifier.

- `hi_stark19_results.txt`, `hi_stark199_construction_results.txt`,
  `hi_stark199_cubic_results.txt`, and `hi_certificate_verification_results.txt`  
  Complete construction, polynomial-identification, and verification logs.

- `hi_stark_prime_power.gp`, `hi_stark25_artin.gp`,
  `hi_stark_single_root.gp`, `hi_stark25_construction_results.txt`, and
  `hi_stark25_verification_results.txt`  
  Prime-power one-root construction, the exact conjugate-prime twist at
  order 25, and its complete independent verification.

- `hi_single_root_checks.gp`, `hi_single_root_results.txt`,
  `hi_prime_power_signs.py`, and `hi_prime_power_signs_results.txt`  
  Exact single-root reconstruction and sign-selection checks, and
  independent off-solution tests of the linear sign identity.

- `hi_stark_cubic_batches.py`  
  Exact integer-polynomial cubic verification in disjoint local batches.

- `hi_beta_reductions.py`, `hi_quadratic_ideal.py`,
  `hi_composite_signs.py`, and their corresponding `_results.txt` files  
  Reproducible beta, ideal-membership and composite sign checks.

- `hi_pell_ray.gp` and `hi_pell_ray_results.txt`  
  Exact fixed-field Lucas-family ray arithmetic and maximal-order RM
  characteristics. These arithmetic tests do not assert HI existence.

- `hi_stark19_partial_results.txt`  
  Exact field and row-root checkpoint at \(n=19\); full matrix
  verification was not completed in the bounded run.

- `hi_phase_reductions.py` and `hi_phase_reductions_results.txt`  
  Reproducible cocycle, binary sign, and Fourier-reduction checks.

- `z17_haagerup_izumi_minpolys.sage`  
  Exact reconstructed \(\mathbb Z_{17}\) minimal-polynomial data.

- `z17_stark_test.gp`  
  Reproducible exact ray-group, Stark-polynomial, field-isomorphism, discriminant, signature, and short-orbit-relation checks for \(p=17\).

- `z7_stark_test.gp`  
  Exact derivation from Evans–Gannon's \(\mathbb Z_7\) solution and the full Stark-orbit comparison.

- `z11_stark_test.gp`  
  Reproducible checks for the two \(p=11\) conductors and branch fields.

- `z13_stark_test.gp`  
  High-precision \(p=13\) reconstruction and exact ray-field, Stark-orbit, discriminant, and Frobenius-\((2)\) checks.

- `z19_ray_test.gp`  
  Exact \(p=19\) class group, ray group, subgroup fields, discriminants, and full Stark-field checks.

- `z19_stark_test.gp`  
  High-precision two-branch reconstruction, exact Hilbert-class factorization and full-ray-field checks, plus the numerical Stark-quotient search.

- `haagerup_izumi_class_field_stark_notes.md`  
  This handoff.
