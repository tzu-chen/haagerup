# PF13 Wick claims: paper pass (ROADMAP W5)

Source: `c8_expanded_20260929/haagerup_c8_expanded.tex`, Proposition
`prop:pf13-finite-reconstruction` (statement 2732–2749, proof 2750–2827; the Wick part is
2750–2813).  Lean: `PF13WickBasic.lean` (general lemmas), `PF13Wick.lean` (the PF13 stages,
`pf13_reconstruction'`, `pf13_reconstruction_of_rows`).  Both files compile; the only axioms are
`propext`, `Classical.choice`, `Quot.sound`.

**Verdict.**  The sketch at lines 2758–2811 is correct, and the acyclic order
`A6 → bb → A7 → bd → B6 → A8 → B7 → dd` works with the stated weight bounds.  Two lemmas are
used implicitly and should be stated (G1, G2 below).  Some wording is imprecise (G3–G5).  One
finding goes beyond the sketch: three hypotheses of the proposition are redundant (G6).

## 1. Setting actually used

* `P` is a weak vertex algebra (`WeakVertexAlgebra`, all interface fields except CFT type).
  The intended instance is `V × V'` (`Diagonal.prodWeak`).
* `S = {L, a, b, d}` has weights 2, 3, 4, 5, with `b = a_(1) a` and `d = a_(1) b`.
  `𝒩 = P.normalSpan S` is the smallest subspace that contains `1` and `S` and is closed under
  `T` and `(-1)`-products.  In `V × V'`, `𝒩` is the diagonal normal span `D`, so
  "`x ∈ 𝒩`" means "`x` is the same normal polynomial in `V` and `V'`".  Membership in `𝒩` is
  the only notion of "known" used.  It needs no freeness.  In characteristic zero `𝒩` is closed
  under all negative modes (`neg_mode_mem`).
* Hypotheses (`PF13Wick.Data`):
  - `L(-1) = T`, `L(0) =` weight, `L_2 L = 0`, `L_3 L = (c/2)1`;
  - `a` is primary;
  - the self-row `a_0 a = ½Tb − (1/12)T³L`, `a_2 a = TL`, `a_3 a = 2L`, `a_4 a = 0`,
    `a_5 a = (c/3)1`;
  - the rows `a_(n) b, a_(n) d ∈ 𝒩`.

  `a_(n) a ∈ 𝒩` follows from the self-row (`PF13.raa_of_selfrow`).
* Notation.  `Rx x f` means `x_(m) y ∈ 𝒩` for every `y ∈ 𝒩 ∩ P_f` and every `m ≥ 0`.  So
  `A_r` is "`Rx a f` for all `f ≤ r`" and `B_r` is the same for `b`.  `Cl p f` means `Rx x f`
  for every `x ∈ 𝒩 ∩ P_p`.  Skew symmetry gives `Cl p f ⇔ Cl f p`.

Instances that `PF13.all_pairs` actually consumes:

| claim | statement | weight of the inner product |
|---|---|---|
| `A6` | `a_m(a_j b)` | `6 − j`; only `j = 0` is new (`a_0 b ∈ 𝒩_6` is an arbitrary normal polynomial) |
| `A7` | `a_m(a_j d)` | `7 − j` |
| `A8` | `a_m(b_j d)` | `8 − j` (needs the `b,d` row first) |
| `B7` | `b_m(a_j d)` | `7 − j` |

Nothing is known about the shape of `a_0 b`, `a_j d`, `b_j d` beyond membership in `𝒩`.  So
each claim is proved for all of `𝒩 ∩ P_{≤ r}`, as in the manuscript.  I see no weaker
targeted statement that would do, but I have not proved that none exists.

## 2. The argument, made precise

**Generic closure** (`lem:filtered-wick` (a), `Weak.closes_of_lt`).  Suppose all generator
pairs of total weight `< w` are known.  Then `Cl p f` holds for all `p + f < w`.
* Before `bb`, the known pairs are `LL, La, aL, Lb, bL, aa, Ld, dL, ab, ba, ad, da`, so
  `w = 8`.
* After `b_n b`, `w = 9`.
* After `b_n d` (and `d_n b` by skew symmetry), `w = 10`.

**Right-normed spanning** (`rnf`).  If `Cl p f` holds for all `p + f < w`, then for
`1 ≤ D ≤ w`, `𝒩 ∩ P_D` is spanned by the monomials `g_(-1-s) u` with `g ∈ S`, `u ∈ 𝒩` and
`wt g + s + wt u = D`.  The proof is a joint induction:
* A word `u_(-1-r) Y` with a composite left factor `u = g_(-1-s) v` is rewritten by the
  iterate formula into `g_(-1-s-t)(v_(t-1-r) Y)` and `v_(-2-s-r-t)(g_(t) Y)`.
* Only pairs of total weight `< D` occur.  Arbitrary parenthesizations are therefore harmless
  through weight 8, because `w = 8` is available from the start.

**Probe lemma** (`probe`).  This is the mode form of the DSK Wick identity on right-normed
monomials:
`x_(m)(g_(-1-s) u) = g_(-1-s)(x_(m) u) + Σ_t (m choose t)(x_(t) g)_(m-1-s-t) u`.
The first term and the negative modes are harmless.  The "Wick integral" is the set of terms
`(x_(t) g)_(k) u` with `k ≥ 0`.  So `Rx x D` follows from three inputs:
1. `Rx x f` for `f < D`;
2. `x_(t) g ∈ 𝒩`;
3. `Rx (x_(t) g) f` for `f ≤ D − wt g`.

Only the terms `t = 0`, `f = D − wt g` lie at the top total weight `wt x + D − 1`
(`Rx_of_top`).  There are two corollaries:
* `Rx_of_gen`: a generator with known row, at the generic level.
* `Cl_of_gens`: `Cl p D` holds once every generator of weight `≤ D` closes against weight
  `p`, with skew symmetry supplying `u_(t) g`.

**The order** (each step in Lean is one line of `PF13Wick.lean`):

| step | how | top-weight inputs |
|---|---|---|
| `L` vs 6, `a` vs 5, `Cl 6 2` | generic (`w = 8`) | `Cl 6 2` needs `L` vs 6 |
| **A6** | `Rx_of_top` | `a_0 L` (from `L_n a`), `a_0 a` (self-row: `b`, `L` vs 3), `a_0 b ∈ 𝒩_6` vs `L` (`Cl 6 2`) |
| `b_n b` | iterate `eq:pf13-b-iterate`, `s = b` | A6 on `a_j b`, weight `≤ 6` |
| `L` vs 7, `Cl 6 3`, `Cl 7 2` | generic (`w = 9`) | uses A6 and `L` vs 6, 7 |
| **A7** | `Rx_of_top` | `a_0 L`; `a_0 a` against weight 4 (**needs `b,b`**); `a_0 b` vs `𝒩_3`; `a_0 d ∈ 𝒩_7` vs `𝒩_2` |
| `b_n d`, `d_n b` | iterate with `s = d`; skew symmetry | A7 on `a_j d`, weight `≤ 7` |
| **B6**, `L` vs 8 | generic (`w = 10`) | none (`L` vs 8 is already available after `b_n b`; see G2) |
| `Cl 6 4`, `Cl 7 3`, `Cl 8 2` | `Cl_of_gens` | need B6, A6, A7, `L` vs 6, 7, 8 |
| **A8** | `Rx_of_top` | `a_0 a` against weight 5 (needs `b,d`); `a_0 b` vs `𝒩_4` (B6); `a_0 d` vs `𝒩_3` (A7) |
| **B7** | `Rx_of_top` | `b_0 L` (from `L_n b`); `b_0 a ∈ 𝒩_6` vs `𝒩_4` (B6); `b_0 b ∈ 𝒩_7` vs `𝒩_3` (A7); `b_0 d ∈ 𝒩_8` vs `𝒩_2` (`L` vs 8) |
| `d_n d` | second iterate identity (line 2808) | A8 on `b_j d`, weight `≤ 8`; B7 on `a_j d`, weight `≤ 7` |

The order is acyclic, and every weight bound stated in the manuscript (lines 2793, 2797,
2811) is the one needed.

## 3. Findings (gaps and imprecisions, with fixes)

**G1 (implicit lemma, lines 2759–2760, "Virasoro creation operators can be moved to the
outside of any normal word using already known commutators").**
* The normal span is closed under `(-1)`-products of arbitrary parenthesization.  Rewriting a
  word into an "outer Virasoro creation operators × core" form, or into any right-normed
  form, uses the OPEs of the composite factors with each other, not only commutators with
  `L`.
* What is true and sufficient: through weight 8, every normal polynomial is a combination of
  right-normed monomials `g_(-1-s) u` (`rnf`).  This uses closure of all pairs of total weight
  `< 8`, which `lem:filtered-wick` (a) gives from the generator rows known at the start.
* **Fix:** add one sentence: "By Lemma `lem:filtered-wick` (a) with `w = 8`, every pair of
  normal polynomials of total weight `≤ 7` closes, so every normal polynomial of weight `≤ 8`
  is a combination of right-normed monomials `g_(-1-s) u`, `g ∈ {L, a, b, d}`."

**G2 (implicit lemma, lines 2773–2775, "Commuting an external `a_n` or `b_n` through outer
Virasoro creation operators reduces their number").**
* For `a_n` this is clean: `[a_(n), L_(-1-j)] = (n + 2j + 2) a_(n-2-j)`.
* For `b_n` it is not.  `[b_λ L]` contains `L`, `TL` and `1`, because
  `L(m) b = (2m+1) a_{m+1} a ∋ TL, L, 1`.  Commuting therefore also produces nonnegative
  Virasoro modes `L_(k)` acting on lower normal polynomials.
* One needs: Virasoro modes preserve `D` on normal polynomials of the relevant weights.  This
  is again `lem:filtered-wick` with `L` as the probe.
* In the right-normed route the Wick-integral coefficients `a_0 b`, `b_0 a ∈ 𝒩_6`,
  `a_0 d`, `b_0 b ∈ 𝒩_7` and `b_0 d ∈ 𝒩_8` must also be bracketed with low-weight normal
  polynomials (Virasoro descendants such as `TL`, `L_{-2}L`, `Ta`), not only with `a`, `b`.
  This needs `Cl 6 2/3/4`, `Cl 7 2/3`, `Cl 8 2`, which follow from A6, B6, A7 and `L`
  against weights 6, 7, 8.
* **Fix:** state that `L_n P ∈ D` for normal `P` of weight `≤ 8` once the rows of total weight
  `≤ 8` are known.  In particular the Virasoro action on weight-8 polynomials needs the `b,b`
  row.  It is available right after `b_n b`, via `Rx_of_top` with the top inputs `TL` vs 6,
  `Ta` vs 5, `Tb` vs 4 and `Td` vs 3.  The Lean file derives it later (after `b_n d`) with
  `Rx_of_gen`, which is enough for its only use in `B7`.

**G3 (lines 2777–2779, definition of `A_r`, `B_r`).**  "The evaluation of `a_n P` on every
normal polynomial `P`" should read:
* "the assertion that `a_n P`, `n ≥ 0`, is given by the same normal polynomial in `V` and
  `V'` (lies in `D`) for every `P ∈ D` of weight `≤ r`".

It must cover all of `D_{≤ r}`, since `a_0 b`, `a_j d`, `b_j d` are arbitrary elements there.

**G4 (lines 2761–2771, table of cores and "Sesquilinearity removes derivatives").**
* The table lists field pairs.  The actual cores also include derivative placements: at weight
  7 `:(Ta)a:` and `:a(Ta):`; at weight 8 `:(T²a)a:`, `:(Ta)(Ta):`, `:(Ta)b:`, `:a(Tb):`, and
  so on.  The reversed orders `:ba:` and `:da:` also occur.  The manuscript does handle
  those, at lines 2772–2773 ("Reversing the order of a core uses skew symmetry and its
  already known pair bracket").
* `:(Ta)(Ta):` is not a derivative of `:aa:` plus lower terms.  Sesquilinearity does not
  "remove" this derivative.  It only lets the Wick identity treat it, through
  `[a_λ Ta] = (λ + T)[a_λ a]`.
* **Fix:** "cores are `:(T^p x)(T^q y):` with `x, y ∈ {a, b, d}`; sesquilinearity reduces their
  brackets to those of the undifferentiated pair".

**G5 (lines 2784–2786 and 2794–2795): the essential use of the self-row should be explicit.**
* The order works only because `a_0 a ∈ span{1, T^p L, T^p b}`, that is, `a_0 a` has no
  `d`-component.
* The `A7` step brackets `a_0 a` with weight-4 polynomials such as `b`.  The `A8` step
  brackets it with weight-5 polynomials such as `d`.  With a term `κ d` in `a_0 a`, `A7` would
  need `d_n b`, which only becomes available after `A7`, and `A8` would need `d_n d`.
* The manuscript says this ("linear in the vacuum and derivatives of `L,b`") but only for
  `A6`, where it is not even needed.  At `A6` the term `a_0 a` against weight 3 is `Cl 5 3`,
  which `Cl_of_gens` gives from `L` and `a` against weight 5.  The Lean proof uses the
  explicit form there anyway.
* The missing `d`-component is automatic.  Skew symmetry with `n = 0` gives, in
  characteristic zero,
  `a_0 a = ½T(a_1 a) − ¼T²(a_2 a) + (1/12)T³(a_3 a) − (1/48)T⁴(a_4 a) + (1/240)T⁵(a_5 a)`.
  With `a_1 a = b`, `a_2 a = TL`, `a_3 a = 2L`, `a_4 a = 0`, `a_5 a ∈ k·1` this is
  `½Tb − (1/12)T³L`.  So the displayed `a_0 a` is itself a consequence of the higher self-row.
  The Lean proof keeps it as the hypothesis `haa0`.
* **Fix:** move the remark to the `A7` sentence and cite this skew-symmetry identity for it.

**G6 (lines 2744–2745, statement): three hypotheses are redundant.**
* Given that the full rows `a_n b` lie in `D`, the assumptions `a_n b = 0` (`n ≥ 4`),
  `a_3 b ∈ ℂa` and `a_2 b ∈ ℂTa` are never used.
* Line 2758 uses them only to make `L(m) d` "linear in generators", which the right-normed
  route does not need.
* `A6` is proved on all of `D_6`, so the reduction `PF13.hA6_of_a0b` (in `PF13Product.lean`)
  is unnecessary too.
* Lean: `pf13_reconstruction_of_rows` has neither these hypotheses nor the four claims.
* **Fix:** either drop them from the proposition, or keep them and remark that they are not
  needed.
  - If they are dropped, line 2758 must change as well, since its claim that the rows are
    "linear in generators and derivatives under the displayed hypotheses" relies on them.
  - Suggested wording: the Virasoro rows "lie in `D`".  Then argue by the right-normed route
    (G1, G2) instead of moving Virasoro creation operators outside.
  - The concluding sentence "`a_1 d` and both simple poles must be specified polynomials"
    stays correct.

Two further observations; no change is needed:
* `B6` needs the `b,d` row only through words `T^s d`.  The manuscript places `B6` after
  `b_n d` (line 2799), which is right.
* `A6` is the only step that does not need any new row.  It needs Virasoro against weight 6
  (Lean) or the Virasoro-outside form (manuscript).

## 4. What remains / changes suggested in existing files (not made)

* Nothing remains for W5.  `PF13Wick.Data.claims` proves the four families of hypotheses of
  `PF13.all_pairs` / `PF13.pf13_reconstruction`.  `PF13Wick.pf13_reconstruction'` is the
  drop-in unconditional version with the same hypotheses minus the claims.
  `PF13Wick.pf13_reconstruction_of_rows` also drops `hab2`, `hab3` and `hab4`.
* Several docstrings still say that the claims are "not yet formalized" or conditional.
  They should point to `PF13Wick.lean`:
  - `PF13.lean`, lines 29–40 and 216–221;
  - `PF13Product.lean`, lines 22–26 and 133–141;
  - `Diagonal.lean`, lines 30–33;
  - `ProofMap.lean`, lines 185–189.  This one also uses the non-existent name
    `PF13Product.pf13_reconstruction`; the theorem is `PF13.pf13_reconstruction`.
* The `L_pf13` node in `ProofMap` can be attached to `PF13Wick.pf13_reconstruction'` (or
  `_of_rows`).
