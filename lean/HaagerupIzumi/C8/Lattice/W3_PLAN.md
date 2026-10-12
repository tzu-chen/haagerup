# W3 plan: the Borcherds identity for the lattice model (state of 4 October 2026, 15:50)

## State of W3 (summary)

The lattice model's single remaining assumption is `FLMBorcherds` (`Lattice/FLMReduce.lean`):
the Borcherds identity for the modes `modeC` of the Fock model.  `flmInput_of_borcherds` is
proved, so `FLMBorcherds` is all that is missing for `latticeVOA`.

**`FLMBorcherds` is now reduced to two statements** (all reductions proved and built, no
`sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only):

```
flmBorcherds_of_generators_iter (hI : fockMA.IterClosed) (hgen : ∀ g ∈ GenSet, fockMA.Good g)
  : FLMBorcherds                                   -- Lattice/FLMBorcherdsIter.lean
flmBorcherds_of_generators_assoc (hA : fockMA.AssocStep) (hgen : ∀ g ∈ GenSet, fockMA.Good g)
  : FLMBorcherds                                   -- same file, via BorcherdsAssocFace.lean
```

1. **Closure of the Borcherds identity under `n`-th products** (an abstract theorem about mode
   algebras, no lattice input).  What is proved:
   - the vacuum;
   - generation;
   - the binomial toolkit;
   - locality and the iterate formula for a `Good` vector;
   - **Dong's lemma for all `n`** (`dong_of_good`).

   What remains is one of the two equivalent-in-effect statements below.  Either one suffices.
   - `IterClosed`: the iterate family `p = 0` for `x = a_(n) w`.
   - `AssocStep`: weak associativity at `p = e + l` for `x = a_(n) w`, given that `a_(n+t) w` is
     `Good` for all `t ≥ 1`.  The downward induction on `n` around it is proved.

   Plan: section 2.  Route A groundwork is in place (section 2.1).  Three things remain
   (section 2.2):
   - the face of the `E`-level defect, which is Li's `E`-level locality lemma and the
     substantive part;
   - the plane of the `E`-level defect;
   - the bridge `ModeAlgebra → OpField`, which is not formalized.

   Estimate: 1.5–2 sessions.
   Only products `g_(n) w` with `g ∈ GenSet` are needed for the lattice model
   (`ProductClosedFor GenSet`, used by `flmBorcherds_of_productClosedFor`).  So generator-only
   variants of `ProductClosedHom`, `IterClosed` and `AssocStep` (`a ∈ GenSet`) would suffice.
   A conversion `ModeAlgebra → BorcherdsVertexAlgebra` (`toBVA` from `∀ a, Good a`) would also
   be useful downstream.
2. **The Borcherds identity for the 24 generator fields** `hᵢ(-1)𝟏`, `e^{±αᵢ}` (model-specific).
   By `good_of_local_iter` this is locality of each generator with every monomial plus its
   iterate formula.  Plan: section 3, via the Heisenberg commutation relations and the FLM
   lattice vertex operator calculus at the mode level (`Lattice/Modes.lean`).  Estimate: several
   sessions.  This is the substantial part of W3.

All files below are built with `c8q build` (exit 0) and end with `#print axioms`.  Dependency
(import) order for C8All:
BorcherdsReduce → BorcherdsVandermonde → BorcherdsClosure → BorcherdsIterate → BorcherdsDong →
BorcherdsDongNeg → BorcherdsDongModes → BorcherdsProduct → BorcherdsAssocFace →
BorcherdsFieldIterate → BorcherdsFields → BorcherdsFieldPair → BorcherdsFieldDong →
BorcherdsFieldE → (Lattice) FLMBorcherdsGen → FLMBorcherdsIter.

## 1. What is proved

### Milestone 1 (morning of 4 October): reduction to generators

* `VertexAlgebra/BorcherdsReduce.lean`
  - `ModeAlgebra` = `BorcherdsVertexAlgebra` without the field `borcherds`.
  - `bL`, `bR`, `bN` and the defect `bD`.
  - `bD_pascal`: `D(p+1,q,r) = D(p,q+1,r) + D(p,q,r+1)`.
  - `bD_eq_zero_of_comm_iter`: the commutator family plus the iterate family imply `D ≡ 0`.
  - `good_vac`: the vacuum is `Good`.
  - `Good`, `goodSub` (a subspace), `good_iff_bD`.
  - `goodSub_eq_top`, `borcherds_of_generation`: generation.
* `VertexAlgebra/BorcherdsClosure.lean`
  - `bD_eq_zero_of_weak`: the two weak faces imply `D ≡ 0`.
  - `commutator_of_good`.
  - `ProductClosedHom`, `goodSub_eq_top_of_hom`.
* `Lattice/FLMBorcherdsGen.lean`
  - `fockMA`, `flmBorcherds_iff_good`.
  - `flmBorcherds_of_generators (hP : fockMA.ProductClosedHom) (hgen) : FLMBorcherds`.

### Item (1), session of 4 October, 14:30–15:10

* (ii) `VertexAlgebra/BorcherdsVandermonde.lean`: binomial toolkit.
  - `zbinom_add` (Chu–Vandermonde over `ℤ`), `zbinom_neg`, `zbinom_natCast_symm`,
    `zbinom_mul_choose`.
  - The locality operator `dz k R F p q = ∑_{t ≤ R} (-1)^t (R choose t) F(p+R-t, q+t)`, i.e.
    `(z₁ - z₂)^R`, with `dz_succ`, `dz_add`, `dz_mono`, `dz_swap` and linearity.
  - `ModeAlgebra.bR_eq_dz`: for `r = R ≥ 0`, `bR = (z₁ - z₂)^R [a(z₁), b(z₂)] c`.
* (i) `VertexAlgebra/BorcherdsIterate.lean`
  - `locality_of_good` and `locality_swap_of_good`: operator form, any `c`.
  - `iterate_of_good`: homogeneous `c`, explicit range.
  - `iterate_op_of_good`: operator form, `r ≥ 0`.
  - A third reduction: `eq_zero_of_pascal_iter_face`, `bD_eq_zero_of_local_iter` and
    **`good_of_local_iter`**.  `Good x` follows from locality of `x` with every homogeneous `b`
    together with the iterate family `p = 0` for `(x, b, c)`.
* (iii) Dong's lemma, **all `n ∈ ℤ`**.
  - `VertexAlgebra/BorcherdsDong.lean`
    - The three-variable operators `d12`, `d13`, `d23` (multiplication by `zᵢ - zⱼ`), which
      commute, with `d23 = d13 - d12`.
    - `d23_pow_eq_zero` (abstract Dong).
    - `dong_natCast` and `ModeAlgebra.dong_of_good_natCast` (the case `n ≥ 0`, with finite sums).
  - `VertexAlgebra/BorcherdsDongNeg.lean`
    - The expansions `ePlus` (`Res_{z₁} i_{z₁,z₂}(z₁-z₂)^n`) and `eMinus` (`i_{z₂,z₁}`), as
      `finsum`s on the subspaces `T2`/`T1` of families vanishing for large second/first index.
    - Linearity, `ePlus_d23_pow` (commutes with `(z₂ - z₃)^R`), `ePlus_d12_pow`
      (`(z₁-z₂)^j i(z₁-z₂)^n = i(z₁-z₂)^{n+j}`, from Pascal's rule) and `ePlus_natCast`
      (polynomial for `n ≥ 0`), plus the same for `eMinus`.
    - **`dong_general`**.
  - `VertexAlgebra/BorcherdsDongModes.lean`
    - `comm_mode_eq_dong`: `[(a_(n)w)_(s), b_(q)] c = ePlus n Φ⁺ - eMinus n Φ⁻`.
    - **`dong_of_good`**: for homogeneous `Good a ∈ V_i`, `Good w ∈ V_m`, any homogeneous
      `b ∈ V_j` and any `n`, `a_(n) w` is local with `b` of order
      `dongOrder i m j n = (2(i+m+j) - n)⁺ + (i+m+j)` on all of `V`.
    - **`good_mode_of_iter`**: `Good (a_(n) w)` follows from the iterate family for
      `(a_(n) w, b, c)`.
* `VertexAlgebra/BorcherdsProduct.lean`: `IterClosed` and
  `productClosedHom_of_iterClosed : IterClosed → ProductClosedHom`.
* `Lattice/FLMBorcherdsIter.lean`: `flmBorcherds_of_generators_iter`, `flmInput_of_generators_iter`,
  and (15:18) `flmBorcherds_of_generators_assoc`.
* `VertexAlgebra/BorcherdsAssocFace.lean` (15:17), for the induction route:
  - `eq_zero_of_pascal_shift_face`: the locality face plus **one** plane `p = P₀` imply `D ≡ 0`.
  - `assoc_face`: for `P ≥ e + l` the defect at `p = P` is the weak-associativity defect.
  - `good_of_local_assoc`: `Good x` from locality plus weak associativity at `p = e + l`.
  - `AssocClosed`, `productClosedHom_of_assocClosed`.
  - `AssocStep` (the induction step), **`good_mode_of_assocStep`** (the downward induction on
    `n`: `a_(n) w = 0` for `n ≥ i + m`), and `productClosedHom_of_assocStep`.

So (ii), (i) and (iii) are done.  (iv) is replaced by `IterClosed` (below), and (v) is done:
`productClosedHom_of_iterClosed` uses the third reduction instead of `bD_eq_zero_of_weak`.

## 2. What remains of item (1): `IterClosed` or `AssocStep`

**Statement** (`ModeAlgebra.IterClosed`): for homogeneous `Good a ∈ V_i`, `Good w ∈ V_m`,
`x = a_(n) w ∈ V_e`, and all homogeneous `b ∈ V_j`, `c ∈ V_l`, and all `q, r`:

`(x_(r) b)_(q) c = ∑_t (-1)^t (r choose t) (x_(r-t) b_(q+t) c - (-1)^r b_(q+r-t) x_(t) c)`

(`bD e j l x b c 0 q r = 0`).

**Reduction to a field identity.**  Expand `x_(r) b` by `iterate_of_good` for `a` on
`(w, b)`.  Then expand `(a_(n-t) (w_(r+t) b))_(q)` and `(w_(n+r-t) (a_(t) b))_(q)` by the
iterate formulas of `a` and `w`.  The left side becomes the "field iterate formula"

`(A_(n) B)_(r) C = ∑_t (-1)^t (n choose t) [A_(n-t) (B_(r+t) C) - (-1)^n B_(n+r-t) (A_(t) C)]`  (*)

for `A = Y(a)`, `B = Y(w)`, `C = Y(b)`, applied to `c`.  Here `F_(k) G` denotes the field
`k`-th product, which is locally finite and is exactly `ePlus`/`eMinus` in two variables.  (*)
holds for any three **pairwise local** fields.  The required localities are available from
`locality_of_good` and `locality_swap_of_good`.

**Proof plan for (*)** (Kac, *Vertex algebras for beginners*, 2nd ed., §4.8, the field form of the
Borcherds identity, numbering checked only against citations in the literature; Lepowsky–Li,
Ch. 3 and Ch. 5, and H. Li, *Local systems of vertex operators, vertex superalgebras and modules*,
JPAA 109 (1996), section numbers from memory):

1. Write both sides of (*) as iterated residues of a three-variable family
   `Ψ(z₁, z₃, z₂) = A(z₃) B(z₁) C(z₂) c` and its reorderings.  At the mode level these are
   nested `ePlus`/`eMinus` in two variable pairs, `(z₃, z₁)` for `A_(n) B` and `(z₁, z₂)` for the
   outer `r`-product.  The `T1`/`T2` machinery of `BorcherdsDongNeg` extends to the other pairs
   by permuting variables.
2. Multiply by a high power `(z₁ - z₂)^K` (locality of `C` with `A` and `B`, via Dong).  On the
   polynomial range (`ePlus_natCast`) both expansions agree.  The difference of the two sides is
   then a combination of `d12`/`d13`/`d23`-images of `[A, C]`- and `[B, C]`-families, which
   vanish.
3. Remove the factor `(z₁ - z₂)^K`.  `dz`-injectivity does not hold in general.  Instead use
   Pascal-type recursions (`ePlus_d12`) to show that the defect of (*) satisfies the hypotheses of
   `eq_zero_of_pascal_iter_face` in the variables `(r, q)`.

**Route B (downward induction on `n`), tried 15:12–15:25.**  The skeleton is formalized and
built (`BorcherdsAssocFace.lean`): `productClosedHom_of_assocStep : AssocStep → ProductClosedHom`.
The open induction step is

`AssocStep`: for homogeneous `Good a ∈ V_i`, `Good w ∈ V_m`, `x = a_(n) w ∈ V_e` with
`a_(n+t) w` `Good` for all `t ≥ 1`, and homogeneous `b ∈ V_j`, `c ∈ V_l`,
`∑_t (P choose t) (x_(r+t) b)_(P+q-t) c = ∑_t (-1)^t (r choose t) x_(P+r-t) b_(q+t) c` at
`P = e + l` (`assoc_face`), for all `q, r`.

What the induction buys.  The Borcherds identity for `(a, w, d)` at `p = K ≥ i + wt d` reads

`∑_t (K choose t) (a_(n+t) w)_(K+s-t) d = ∑_t (-1)^t (n choose t) a_(K+n-t) w_(s+t) d`.  (★)

It expresses a mode of `x` on `d` through `a`–`w` words and modes of the `Good` vectors
`a_(n+t) w`, `t ≥ 1`.  Combining (★) over `t` turns the `IH` terms into complete Borcherds
defects of `a_(n+t) w`, which vanish.

Why it did not close.  In the associativity defect of `x`:
- the second sum needs (★) for the targets `d = b_(q+t) c`, whose weights are unbounded as
  `q → -∞`, so `K` must depend on `q`;
- the first sum needs the vectors `x_(k) b` (from (★) with `d = b`), whose modes on `c` then need
  weak associativity of `a` with the second vectors `w_(·) b` and of `w` with `b`.

The twist by `(z₁ + z₀)^K` in (★) becomes `(z₁ + z₁' - z₂)^K` after the Jacobi substitution
`z₀ = z₁' - z₂`, and expanding that reintroduces small powers, where (★) does not apply.
Handling this is the classical formal-calculus argument (FHL / Lepowsky–Li style).  At the mode
level it is a three-fold binomial convolution with grade-dependent cut-offs, and it is the same
amount of work as route A.  So route B is **not** shorter.  Its gain is that the base case and
the induction are already formal.

**Revised estimate.** 1.5–2 sessions, about 400–600 lines, for either route.  The
`dz`/`ePlus`/`eMinus` infrastructure is reusable as is.  The main new ingredient is nested
expansions in two pairs of variables (route A), or the two-step weak-associativity computation
with `q`-dependent `K` (route B).  Recommendation: route A, because (*) is a clean statement
about three pairwise local operator families and the three-variable calculus of `dong_general`
transfers directly.

### 2.1 Route A groundwork (15:20–15:35, all built)

These are abstract fields on a vector space, with no mode algebra and no grading.

* `VertexAlgebra/BorcherdsFieldIterate.lean` (log `done/152319-fd45c7`): the **decomposition
  theorem** (Kac, VAfB, Theorem 2.3; number from memory).
  - `deltaFam j c (p, q) = (p choose j) c(p+q-j)`, the coefficients of `c(z₂) ∂^{(j)} δ(z₁-z₂)`.
  - `dz_deltaFam_le` and `dz_deltaFam_gt`.
  - `res_deltaFam`: `Res (z₁-z₂)^i ∂^{(j)} δ = δ_{ij}`.
  - `eq_zero_of_dz_res`: uniqueness.
  - **`eq_sum_of_dz_eq_zero`**: `(z₁-z₂)^N F = 0 ⇒ F(p,q) = ∑_{j<N} (p choose j) c_j(p+q-j)`,
    with `c_j(s) = dz j F (0, s)`.
  - `commutator_of_local`.
* `VertexAlgebra/BorcherdsFields.lean` (log `done/152506-3c96f4`): fields and their products.
  - `OpField k V`: an operator family with `A_u v = 0` for `u ≫ 0`.
  - `OpField.prod n A B`: the field `n`-th product, as linear maps via `finsum`; it is again a
    field.
  - `prodMode_eq_sum`: the finite-sum form.
  - `prod_natCast_eq_dz`: `(A_(N) B)_s = dz N [A,B] (0,s)`.
  - `prod_eq_zero_of_local` and `commutator_of_local_prod`.
* `VertexAlgebra/BorcherdsFieldPair.lean` (log `done/152759-765aa7`):
  **`OpField.borcherds_of_local`**.  For fields `A, B` local of order `N`, the full Borcherds
  identity holds on every `v` with the field products `A_(n) B`.  This is the mode form of the
  Jacobi identity for a local pair.  The proof uses `fD_pascal`, then `fD_iter` (the iterate
  plane is the definition of the product) and `fD_face` (locality), then
  `eq_zero_of_pascal_iter_face`.  Also `ysum_sub_eq_dz`.
* `VertexAlgebra/BorcherdsFieldDong.lean` (log `done/153109-0498ce`):
  - `OpField.IsLocal`.
  - **`OpField.dong`**: if `A, B, C` are pairwise local of order `r`, then `A_(n) B` is local
    with `C` of order `(2r-n)⁺ + r`, for all `n ∈ ℤ`.  This uses `dong_general` with
    `comm_prod_eq`, `dong_h12`, `dong_h3p` and `dong_h3m`.
  - **`OpField.assoc_of_local`**: weak associativity on `V`,
    `∑_t (p choose t) (A_(r+t)B)_{p+q-t} v = ∑_t (-1)^t (r choose t) A_{p+r-t} B_{q+t} v`
    for `p ≥ P₀(A, v)`.
  - **`eq_zero_of_dz_of_trunc`**: multiplication by `(z₁-z₂)^R` is injective on families
    truncated in the second variable.  This is the cancellation step of Li's argument.

* `VertexAlgebra/BorcherdsFieldE.lean` (log `done/153318-5af64c`): the `E`-level defect
  `OpField.eD A B C N s v p q r`, at the mode `s` on `v`, with ranges from the locality order.
  - `prod_eq_zero_left`, `prod_eq_zero_right` and `prod_eq_zero_of_local'`.
  - **`eD_pascal`**: step 1 below.
  - **`eD_eq_zero_of_face_plane`**: step 4.
  - **`fieldIter_of_eD`**: the plane `p = 0` of `eD` is the field iterate identity.

### 2.2 The precise next lemma (route A)

**`fieldIter`** (the field iterate identity).  Let `A, B, C : OpField k V` be pairwise local of
order `r`.  Then for all `n, m, s ∈ ℤ` and `v`:

`((A_(n)B)_(m) C)_s v = ∑_t (-1)^t (n choose t) [ (A_(n-t) (B_(m+t) C))_s v
                                                  - (-1)^n (B_(n+m-t) (A_(t) C))_s v ]`.

The `t`-sum is finite: `A_(t) C = 0` for `t ≥ r` and `B_(m+t) C = 0` for `m + t ≥ r`, by
`prod_eq_zero_of_local`.  The proof plan reuses the existing reductions on the
"E-level" defect `G(p,q,r) = ∑_t (p choose t) (A_(r+t)B)_(p+q-t) C - ∑_t (-1)^t (r choose t)
(A_(p+r-t)(B_(q+t)C) - (-1)^r B_(q+r-t)(A_(p+t)C))` (field valued; `fieldIter` is `G(0, m, n) = 0`):

1. Pascal recursion for `G`.  This is formal, a copy of `fD_pascal`, with ranges from
   `prod_eq_zero_of_local`.
2. A locality face `r ≥ R₀` for `G`.  This is Li's `E`-level locality lemma, the locality of
   the operators `C ↦ A_(p) C` and `C ↦ B_(q) C` on fields, and it is the **substantive part**
   of route A.  Plan: evaluate on `v`, apply `assoc_of_local` to the pairs `(A, B_(·)C)` and
   `(B, C)` (and symmetrically), multiply by `(z₁ - z₂)^N`, and cancel the binomial factors with
   a `(z + z')` variant of `eq_zero_of_dz_of_trunc`.
3. One plane `p = P₀`, weak associativity of the `E`-action.  Prove it on each `v` with
   `assoc_of_local` for the pairs `(A_(·)B, C)`, `(A, B_(·)C)`, `(A, B)`, `(B, C)`.  Then cancel
   the common binomial factor with `eq_zero_of_dz_of_trunc` (a `(z₀ + z₂)` variant is needed,
   with the same proof).
4. Conclude with `eq_zero_of_pascal_shift_face` (`BorcherdsAssocFace.lean`).

5. **The bridge `ModeAlgebra → OpField`** (open; not formalized; estimate 100–200 lines).
   - (i) `Y(a)` as an `OpField`.  Truncation on arbitrary `v` uses the decomposition of `v` into
     finitely many graded pieces (`grade_internal`, `Submodule.iSup_induction`).
   - (ii) `(prod k (Y a) (Y u)).mode = M.mode · (a_(k) u)` for homogeneous `Good a` and all `u`.
     This is `iterate_of_good` together with `prodMode_eq_sum`, plus the extension from
     homogeneous `u` to all `u`.
   - (iii) `fieldIter ⇒ IterClosed`.  Expand `x_(r) b` with `x = a_(n) w` by `iterate_of_good`
     and (ii), and match the ranges of `eD` (locality-order ranges) with those of `bD`
     (`bN` ranges) via the stability lemmas.

**Status (15:50).**  Steps 1 and 4 are proved (`eD_pascal`, `eD_eq_zero_of_face_plane`,
`fieldIter_of_eD`).  Open: steps 2, 3 and 5.  Steps 2 and 3 are the two hypotheses of
`eD_eq_zero_of_face_plane`, for pairwise local `A, B, C` of order `N` and every `s`, `v`:

* **(face)** `∀ p q r, R₀ ≤ r → eD A B C N s v p q r = 0`, for some `R₀`.  Since
  `A_(r+t) B = 0` for `r ≥ N`, this is the locality of the operators `C ↦ A_(p) C` and
  `C ↦ B_(q) C` on fields, evaluated at `(s, v)`.
* **(plane)** `∀ q r, eD A B C N s v P₀ q r = 0`, for some `P₀ ≥ N`, which may depend on
  `s, v`.  For `P₀ ≥ N` the `B (A C)` part vanishes (`A_(P₀+t) C = 0`), so this is the weak
  associativity of the `E`-action.

Remark on (plane).  Li's cancellation multiplies by `(z₂ + z₃)^K` (`assoc_of_local` for the pairs
`(A_(j)B, C)` and `(A, B_(j)C)` on `v`), which mixes the index `q` with the mode `s`.  So (plane)
should be proved for the family `(q, s) ↦ eD(P₀, q, r)` at fixed `r, v`, and then cancelled with
a `(z₂ + z₃)` variant of `eq_zero_of_dz_of_trunc`, truncated in `s` by the field truncation of
`C` on `v`.

Estimate for the open steps: (face) is Li's `E`-level locality lemma and the substantive part,
about 1 session; (plane) about 0.5 session; the bridge (step 5) is 100–200 lines.  Total 1.5–2
sessions.

## 3. The Borcherds identity for the 24 generator fields (open; the hard remaining part)

`Good g` for `g ∈ GenSet = {hᵢ(-1)𝟏, e^{±αᵢ}}` is the Borcherds identity with a generator in
the first slot and **arbitrary** `b, c`.  By `good_of_local_iter` (or `bD_eq_zero_of_comm_iter`)
it splits into:

* (a) **locality** of `g` with every homogeneous `b` (some order), or the commutator formula
  `[g_(m), b_(n)] = ∑_t (m choose t) (g_(t) b)_(m+n-t)`;
* (b) the **iterate formula** for `(g, b)`, all `b`.

Suggested route: the lattice vertex operator construction (FLM, *Vertex operator algebras and the
Monster*, Ch. 7–8; Kac, VAfB, §5.4–5.5; Lepowsky–Li, Ch. 6; section numbers from memory), adapted
to the model.

1. **Heisenberg generator `g = hᵢ(-1)𝟏`.**
   - `g_(n)` is the Heisenberg operator `hᵢ(n)`.  `modeC_hV` (`Lattice/FLMGen.lean`) gives this
     for creation; prove it for all `n` from `toFock_basisModeAux_h` and `basisModeAux`
     (`Lattice/Modes.lean`).
   - (a) is `[hᵢ(m), Y(b,z)] = ∑_t (m choose t) Y(hᵢ(t) b, z) z^{m-t}`.  Prove it by induction
     on the canonical monomial `b` (the normal-ordered recursion defining `basisMode`), using
     `[hᵢ(m), hⱼ(n)] = m (αᵢ, αⱼ) δ_{m+n,0}` and `[hᵢ(m), e^β-part] = (αᵢ, β) …`.
   - (b) for `n < 0` is the normal-ordering recursion of `basisMode` (essentially definitional,
     to be checked against `Lattice/Modes.lean`).  For `n ≥ 0` it follows from (a) and creation.
2. **Lattice generator `g = e^α`, `α = ±αᵢ`.**
   - `Y(e^α, z) = E⁻(-α, z) E⁺(-α, z) e_α z^α`, with the cocycle `Mom.eps`
     (`Lattice/Fock.lean`).
   - The key fact is the FLM commutator `[hᵢ(m), Y(e^α, z)] = (αᵢ, α) z^m Y(e^α, z)`.
   - The product formula `Y(e^α,z₁) Y(e^β,z₂) = ε(α,β) (z₁-z₂)^{(α,β)} :Y(e^α,z₁)Y(e^β,z₂):`
     gives locality of `e^α` with every `e^β`.
   - Locality with every monomial must **not** use `dong_of_good`: it needs both factors `Good`,
     so using it before `Good g` is known would be circular.  Instead use `OpField.dong` on the
     fields `Y(g)`, `Y(w)`.  Induct on the length of the monomial `w = g'_(n) w'`.
     The hypothesis is that the generator fields are pairwise local and each is local with
     `Y(w')`.  The generator iterate formula (b) identifies `Y(g'_(n) w')` with the field product
     `Y(g')_(n) Y(w')`.  `OpField.dong` with `A = Y(g')`, `B = Y(w')`, `C = Y(g)` then gives the
     locality of `Y(g)` with it.
   - At the mode level: the `schur`/`contract` combinatorics of `Lattice/Modes.lean`.
3. **Cheaper intermediate targets** (kernel-checkable sanity, not proofs):
   - `bD = 0` for each generator `g` against a few small monomials at small `p, q, r`, as a
     regression test of the modes (cf. the 822 `basisMode` samples of `Lattice/Samples*.lean`);
   - the 24 × 24 generator–generator localities, in finitely many orbits.

Section 3 (items 1 and 2; item 3 is only sanity checks) is the substantial part of W3 (several
sessions).
