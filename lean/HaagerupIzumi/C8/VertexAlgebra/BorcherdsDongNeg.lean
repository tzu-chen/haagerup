module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsDong

@[expose] public section

/-!
# Dong's lemma for all `n`: the expansions `i_{z₁,z₂}(z₁ - z₂)^n` and `i_{z₂,z₁}(z₁ - z₂)^n`

W3, item (1), step (iii) of `Lattice/W3_PLAN.md`, abstract part for arbitrary `n ∈ ℤ`.  For a
three-variable family `Ψ : ℤ → ℤ → ℤ → W`:

* `ePlus k n Ψ v w = ∑_{t ≥ 0} (-1)^t (n choose t) Ψ(n - t, v + t, w)`, the coefficient of
  `z₂^{-v-1} z₃^{-w-1}` in `Res_{z₁} i_{z₁,z₂}(z₁ - z₂)^n Ψ(z₁, z₂, z₃)` (a finite sum on the
  subspace `T2` of families vanishing for large second index);
* `eMinus k n Ψ v w = ∑_{t ≥ 0} (-1)^{n+t} (n choose t) Ψ(t, n + v - t, w)`, the same with
  `i_{z₂,z₁}` (finite on the subspace `T1` of families vanishing for large first index).

Proved: linearity (`ePlus_add`, `ePlus_smul`, `ePlus_sum`, and for `eMinus`),
`ePlus_d23_pow` (`(z₂ - z₃)^R` commutes with the expansions), `ePlus_d12_pow`
(`(z₁ - z₂)^j i(z₁ - z₂)^n = i(z₁ - z₂)^{n+j}`, from Pascal's rule), `ePlus_natCast` (for
`n ≥ 0` both expansions are the polynomial `(z₁ - z₂)^n`), and

* **`dong_general`** (Dong's lemma, abstract form, all `n`): if `Φ⁺ ∈ T2`, `Φ⁻ ∈ T1`,
  `d12^r (Φ⁺ - Φ⁻) = 0` and `d13^r d23^r Φ^± = 0`, then `(z₂ - z₃)^{L + r} (ePlus n Φ⁺ - eMinus n Φ⁻) = 0` whenever
  `2r ≤ n + L`.  The proof is that of Kac, *Vertex algebras for beginners*, 2nd ed., Lemma 3.2
  (Dong's lemma; numbering checked only against citations in the literature): expand `(z₂ - z₃)^L = ∑_s (L choose s) (z₁ - z₃)^s (z₂ - z₁)^{L-s}`;
  the terms with `s ≥ r` die by `d13^r d23^r Φ^± = 0`, those with `s < r` because
  `i(z₁ - z₂)^n (z₁ - z₂)^{L-s}` is the polynomial `(z₁ - z₂)^{n+L-s}`, `n + L - s ≥ r`.

The application to modes (`Φ⁺ = A B C - C A B`, `Φ⁻ = B A C - C B A` applied to a vector) is in
`VertexAlgebra/BorcherdsDongModes.lean`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

section Expansions

variable (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W]

/-- Families vanishing for large second index, uniformly in the first. -/
def T2 : Submodule k (ℤ → ℤ → ℤ → W) where
  carrier := {Ψ | ∀ w, ∃ N : ℤ, ∀ u v, N ≤ v → Ψ u v w = 0}
  zero_mem' := fun _ => ⟨0, fun _ _ _ => rfl⟩
  add_mem' := by
    intro Ψ Ψ' h h' w
    obtain ⟨N, hN⟩ := h w
    obtain ⟨N', hN'⟩ := h' w
    exact ⟨max N N', fun u v hv => by
      show Ψ u v w + Ψ' u v w = 0
      rw [hN u v (le_of_max_le_left hv), hN' u v (le_of_max_le_right hv), add_zero]⟩
  smul_mem' := by
    intro μ Ψ h w
    obtain ⟨N, hN⟩ := h w
    exact ⟨N, fun u v hv => by
      show μ • Ψ u v w = 0
      rw [hN u v hv, smul_zero]⟩

/-- Families vanishing for large first index, uniformly in the second. -/
def T1 : Submodule k (ℤ → ℤ → ℤ → W) where
  carrier := {Ψ | ∀ w, ∃ N : ℤ, ∀ u v, N ≤ u → Ψ u v w = 0}
  zero_mem' := fun _ => ⟨0, fun _ _ _ => rfl⟩
  add_mem' := by
    intro Ψ Ψ' h h' w
    obtain ⟨N, hN⟩ := h w
    obtain ⟨N', hN'⟩ := h' w
    exact ⟨max N N', fun u v hu => by
      show Ψ u v w + Ψ' u v w = 0
      rw [hN u v (le_of_max_le_left hu), hN' u v (le_of_max_le_right hu), add_zero]⟩
  smul_mem' := by
    intro μ Ψ h w
    obtain ⟨N, hN⟩ := h w
    exact ⟨N, fun u v hu => by
      show μ • Ψ u v w = 0
      rw [hN u v hu, smul_zero]⟩

variable {W}

/-- `Res_{z₁} i_{z₁,z₂}(z₁ - z₂)^n Ψ`. -/
noncomputable def ePlus (n : ℤ) (Ψ : ℤ → ℤ → ℤ → W) (v w : ℤ) : W :=
  ∑ᶠ t : ℕ, ((-1 : k) ^ t * zbinom k n t) • Ψ (n - t) (v + t) w

/-- `Res_{z₁} i_{z₂,z₁}(z₁ - z₂)^n Ψ`. -/
noncomputable def eMinus (n : ℤ) (Ψ : ℤ → ℤ → ℤ → W) (v w : ℤ) : W :=
  ∑ᶠ t : ℕ, ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) • Ψ t (n + v - t) w

variable {k}

theorem mem_T2 {Ψ : ℤ → ℤ → ℤ → W} :
    Ψ ∈ T2 k W ↔ ∀ w, ∃ N : ℤ, ∀ u v, N ≤ v → Ψ u v w = 0 := Iff.rfl

theorem mem_T1 {Ψ : ℤ → ℤ → ℤ → W} :
    Ψ ∈ T1 k W ↔ ∀ w, ∃ N : ℤ, ∀ u v, N ≤ u → Ψ u v w = 0 := Iff.rfl

theorem pow_mem_of {M' : Type*} [AddCommGroup M'] [Module k M'] {S : Submodule k M'}
    {f : Module.End k M'} (hf : ∀ x ∈ S, f x ∈ S) (j : ℕ) : ∀ x ∈ S, (f ^ j) x ∈ S := by
  induction j with
  | zero => intro x hx; rwa [pow_zero, Module.End.one_apply]
  | succ j ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih x hx)

theorem d12_mem_T2 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) : d12 k W Ψ ∈ T2 k W :=
  mem_T2.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T2.1 h w
    exact ⟨N, fun u v hv => by rw [d12_apply, hN _ _ hv, hN u (v + 1) (by omega), sub_zero]⟩

theorem d13_mem_T2 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) : d13 k W Ψ ∈ T2 k W :=
  mem_T2.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T2.1 h w
    obtain ⟨N', hN'⟩ := mem_T2.1 h (w + 1)
    exact ⟨max N N', fun u v hv => by
      rw [d13_apply, hN _ _ (le_of_max_le_left hv), hN' _ _ (le_of_max_le_right hv), sub_zero]⟩

theorem d23_mem_T2 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) : d23 k W Ψ ∈ T2 k W :=
  mem_T2.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T2.1 h w
    obtain ⟨N', hN'⟩ := mem_T2.1 h (w + 1)
    exact ⟨max N N', fun u v hv => by
      rw [d23_apply, hN u (v + 1) (by omega), hN' _ _ (le_of_max_le_right hv), sub_zero]⟩

theorem d12_mem_T1 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) : d12 k W Ψ ∈ T1 k W :=
  mem_T1.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T1.1 h w
    exact ⟨N, fun u v hu => by rw [d12_apply, hN (u + 1) v (by omega), hN _ _ hu, sub_zero]⟩

theorem d13_mem_T1 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) : d13 k W Ψ ∈ T1 k W :=
  mem_T1.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T1.1 h w
    obtain ⟨N', hN'⟩ := mem_T1.1 h (w + 1)
    exact ⟨max N N', fun u v hu => by
      rw [d13_apply, hN (u + 1) v (by omega), hN' _ _ (le_of_max_le_right hu), sub_zero]⟩

theorem d23_mem_T1 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) : d23 k W Ψ ∈ T1 k W :=
  mem_T1.2 fun w => by
    obtain ⟨N, hN⟩ := mem_T1.1 h w
    obtain ⟨N', hN'⟩ := mem_T1.1 h (w + 1)
    exact ⟨max N N', fun u v hu => by
      rw [d23_apply, hN _ _ (le_of_max_le_left hu), hN' _ _ (le_of_max_le_right hu), sub_zero]⟩

theorem d12_pow_mem_T2 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) :
    ((d12 k W) ^ j) Ψ ∈ T2 k W := pow_mem_of (S := T2 k W) (fun _ hx => d12_mem_T2 hx) j Ψ h

theorem d13_pow_mem_T2 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) :
    ((d13 k W) ^ j) Ψ ∈ T2 k W := pow_mem_of (S := T2 k W) (fun _ hx => d13_mem_T2 hx) j Ψ h

theorem d23_pow_mem_T2 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) :
    ((d23 k W) ^ j) Ψ ∈ T2 k W := pow_mem_of (S := T2 k W) (fun _ hx => d23_mem_T2 hx) j Ψ h

theorem d12_pow_mem_T1 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) :
    ((d12 k W) ^ j) Ψ ∈ T1 k W := pow_mem_of (S := T1 k W) (fun _ hx => d12_mem_T1 hx) j Ψ h

theorem d13_pow_mem_T1 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) :
    ((d13 k W) ^ j) Ψ ∈ T1 k W := pow_mem_of (S := T1 k W) (fun _ hx => d13_mem_T1 hx) j Ψ h

theorem d23_pow_mem_T1 (j : ℕ) {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) :
    ((d23 k W) ^ j) Ψ ∈ T1 k W := pow_mem_of (S := T1 k W) (fun _ hx => d23_mem_T1 hx) j Ψ h

/-! ### Finite-sum representations -/

theorem ePlus_eq_sum {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (n v w : ℤ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ePlus k n Ψ v w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k n t) • Ψ (n - t) (v + t) w := by
  obtain ⟨B, hB⟩ := mem_T2.1 h w
  refine ⟨(B - v).toNat, fun N hN => finsum_eq_sum_of_support_subset _ fun t ht => ?_⟩
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact ht (by dsimp only; rw [hB (n - t) (v + t) (by omega), smul_zero])

theorem eMinus_eq_sum {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (n v w : ℤ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → eMinus k n Ψ v w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) •
        Ψ t (n + v - t) w := by
  obtain ⟨B, hB⟩ := mem_T1.1 h w
  refine ⟨B.toNat, fun N hN => finsum_eq_sum_of_support_subset _ fun t ht => ?_⟩
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact ht (by dsimp only; rw [hB t (n + v - t) (by omega), smul_zero])

theorem ePlus_zero (n v w : ℤ) : ePlus k n (0 : ℤ → ℤ → ℤ → W) v w = 0 := by
  simp [ePlus]

theorem eMinus_zero (n v w : ℤ) : eMinus k n (0 : ℤ → ℤ → ℤ → W) v w = 0 := by
  simp [eMinus]

/-! ### Linearity -/

theorem ePlus_add {Ψ Ψ' : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (h' : Ψ' ∈ T2 k W) (n v w : ℤ) :
    ePlus k n (Ψ + Ψ') v w = ePlus k n Ψ v w + ePlus k n Ψ' v w := by
  obtain ⟨N₁, h₁⟩ := ePlus_eq_sum h n v w
  obtain ⟨N₂, h₂⟩ := ePlus_eq_sum h' n v w
  obtain ⟨N₃, h₃⟩ := ePlus_eq_sum (Submodule.add_mem _ h h') n v w
  rw [h₁ (N₁ + N₂ + N₃) (by omega), h₂ (N₁ + N₂ + N₃) (by omega),
    h₃ (N₁ + N₂ + N₃) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, smul_add]

theorem eMinus_add {Ψ Ψ' : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (h' : Ψ' ∈ T1 k W) (n v w : ℤ) :
    eMinus k n (Ψ + Ψ') v w = eMinus k n Ψ v w + eMinus k n Ψ' v w := by
  obtain ⟨N₁, h₁⟩ := eMinus_eq_sum h n v w
  obtain ⟨N₂, h₂⟩ := eMinus_eq_sum h' n v w
  obtain ⟨N₃, h₃⟩ := eMinus_eq_sum (Submodule.add_mem _ h h') n v w
  rw [h₁ (N₁ + N₂ + N₃) (by omega), h₂ (N₁ + N₂ + N₃) (by omega),
    h₃ (N₁ + N₂ + N₃) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, smul_add]

theorem ePlus_smul {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (μ : k) (n v w : ℤ) :
    ePlus k n (μ • Ψ) v w = μ • ePlus k n Ψ v w := by
  obtain ⟨N₁, h₁⟩ := ePlus_eq_sum h n v w
  obtain ⟨N₂, h₂⟩ := ePlus_eq_sum (Submodule.smul_mem _ μ h) n v w
  rw [h₁ (N₁ + N₂) (by omega), h₂ (N₁ + N₂) (by omega), Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_comm]

theorem eMinus_smul {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (μ : k) (n v w : ℤ) :
    eMinus k n (μ • Ψ) v w = μ • eMinus k n Ψ v w := by
  obtain ⟨N₁, h₁⟩ := eMinus_eq_sum h n v w
  obtain ⟨N₂, h₂⟩ := eMinus_eq_sum (Submodule.smul_mem _ μ h) n v w
  rw [h₁ (N₁ + N₂) (by omega), h₂ (N₁ + N₂) (by omega), Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_comm]

theorem ePlus_sum {ι : Type*} (S : Finset ι) (Ψ : ι → ℤ → ℤ → ℤ → W)
    (h : ∀ s ∈ S, Ψ s ∈ T2 k W) (n v w : ℤ) :
    ePlus k n (∑ s ∈ S, Ψ s) v w = ∑ s ∈ S, ePlus k n (Ψ s) v w := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ePlus_zero]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      ePlus_add (h x (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun s hs => h s (Finset.mem_insert_of_mem hs)),
      ih fun s hs => h s (Finset.mem_insert_of_mem hs)]

theorem eMinus_sum {ι : Type*} (S : Finset ι) (Ψ : ι → ℤ → ℤ → ℤ → W)
    (h : ∀ s ∈ S, Ψ s ∈ T1 k W) (n v w : ℤ) :
    eMinus k n (∑ s ∈ S, Ψ s) v w = ∑ s ∈ S, eMinus k n (Ψ s) v w := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, eMinus_zero]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      eMinus_add (h x (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun s hs => h s (Finset.mem_insert_of_mem hs)),
      ih fun s hs => h s (Finset.mem_insert_of_mem hs)]

/-! ### `(z₂ - z₃)` commutes with the expansions -/

theorem ePlus_d23 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (n v w : ℤ) :
    ePlus k n (d23 k W Ψ) v w = ePlus k n Ψ (v + 1) w - ePlus k n Ψ v (w + 1) := by
  obtain ⟨N₁, h₁⟩ := ePlus_eq_sum h n (v + 1) w
  obtain ⟨N₂, h₂⟩ := ePlus_eq_sum h n v (w + 1)
  obtain ⟨N₃, h₃⟩ := ePlus_eq_sum (d23_mem_T2 h) n v w
  rw [h₁ (N₁ + N₂ + N₃) (by omega), h₂ (N₁ + N₂ + N₃) (by omega),
    h₃ (N₁ + N₂ + N₃) (by omega), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [d23_apply, smul_sub, show v + 1 + (t : ℤ) = v + t + 1 by ring]

theorem eMinus_d23 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (n v w : ℤ) :
    eMinus k n (d23 k W Ψ) v w = eMinus k n Ψ (v + 1) w - eMinus k n Ψ v (w + 1) := by
  obtain ⟨N₁, h₁⟩ := eMinus_eq_sum h n (v + 1) w
  obtain ⟨N₂, h₂⟩ := eMinus_eq_sum h n v (w + 1)
  obtain ⟨N₃, h₃⟩ := eMinus_eq_sum (d23_mem_T1 h) n v w
  rw [h₁ (N₁ + N₂ + N₃) (by omega), h₂ (N₁ + N₂ + N₃) (by omega),
    h₃ (N₁ + N₂ + N₃) (by omega), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [d23_apply, smul_sub, show n + (v + 1) - (t : ℤ) = n + v - t + 1 by ring]

theorem ePlus_d23_pow {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (n : ℤ) (R : ℕ) :
    ∀ v w, ePlus k n (((d23 k W) ^ R) Ψ) v w = dz k R (ePlus k n Ψ) v w := by
  induction R with
  | zero => intro v w; rw [pow_zero, Module.End.one_apply, dz_zero]
  | succ R ih =>
    intro v w
    rw [pow_succ', Module.End.mul_apply,
      ePlus_d23 (d23_pow_mem_T2 R h), ih, ih, dz_succ]

theorem eMinus_d23_pow {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (n : ℤ) (R : ℕ) :
    ∀ v w, eMinus k n (((d23 k W) ^ R) Ψ) v w = dz k R (eMinus k n Ψ) v w := by
  induction R with
  | zero => intro v w; rw [pow_zero, Module.End.one_apply, dz_zero]
  | succ R ih =>
    intro v w
    rw [pow_succ', Module.End.mul_apply,
      eMinus_d23 (d23_pow_mem_T1 R h), ih, ih, dz_succ]

/-! ### `(z₁ - z₂) i(z₁ - z₂)^n = i(z₁ - z₂)^{n+1}` -/

theorem ePlus_d12 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T2 k W) (n v w : ℤ) :
    ePlus k n (d12 k W Ψ) v w = ePlus k (n + 1) Ψ v w := by
  obtain ⟨B, hB⟩ := mem_T2.1 h w
  obtain ⟨N₁, h₁⟩ := ePlus_eq_sum (d12_mem_T2 h) n v w
  obtain ⟨N₂, h₂⟩ := ePlus_eq_sum h (n + 1) v w
  obtain ⟨N, hN1, hN2, hNB⟩ : ∃ N : ℕ, N₁ ≤ N ∧ N₂ ≤ N ∧ B ≤ v + N :=
    ⟨N₁ + N₂ + (B - v).toNat, by omega, by omega, by omega⟩
  rw [h₁ (N + 1) (by omega), h₂ (N + 1) (by omega)]
  simp only [d12_apply, smul_sub, Finset.sum_sub_distrib]
  have key : ∀ t ∈ Finset.range N,
      ((-1 : k) ^ (t + 1) * zbinom k (n + 1) (t + 1)) •
          Ψ (n + 1 - ((t + 1 : ℕ) : ℤ)) (v + ((t + 1 : ℕ) : ℤ)) w =
        ((-1 : k) ^ (t + 1) * zbinom k n (t + 1)) •
            Ψ (n - ((t + 1 : ℕ) : ℤ) + 1) (v + ((t + 1 : ℕ) : ℤ)) w -
          ((-1 : k) ^ t * zbinom k n t) • Ψ (n - (t : ℤ)) (v + (t : ℤ) + 1) w := by
    intro t _
    have e1 : n + 1 - ((t + 1 : ℕ) : ℤ) = n - (t : ℤ) := by push_cast; ring
    have e2 : n - ((t + 1 : ℕ) : ℤ) + 1 = n - (t : ℤ) := by push_cast; ring
    have e3 : v + ((t + 1 : ℕ) : ℤ) = v + (t : ℤ) + 1 := by push_cast; ring
    rw [e1, e2, e3, zbinom_succ_succ, pow_succ]
    module
  have hR : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ t * zbinom k (n + 1) t) •
        Ψ (n + 1 - (t : ℤ)) (v + (t : ℤ)) w =
      ∑ t ∈ Finset.range N, (((-1 : k) ^ (t + 1) * zbinom k n (t + 1)) •
            Ψ (n - ((t + 1 : ℕ) : ℤ) + 1) (v + ((t + 1 : ℕ) : ℤ)) w -
          ((-1 : k) ^ t * zbinom k n t) • Ψ (n - (t : ℤ)) (v + (t : ℤ) + 1) w) +
        Ψ (n + 1) v w := by
    rw [Finset.sum_range_succ', Finset.sum_congr rfl key]
    simp only [Nat.cast_zero, sub_zero, add_zero, pow_zero, zbinom_zero_right, one_mul,
      one_smul]
  have hL1 : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ t * zbinom k n t) •
        Ψ (n - (t : ℤ) + 1) (v + (t : ℤ)) w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ (t + 1) * zbinom k n (t + 1)) •
          Ψ (n - ((t + 1 : ℕ) : ℤ) + 1) (v + ((t + 1 : ℕ) : ℤ)) w + Ψ (n + 1) v w := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, sub_zero, add_zero, pow_zero, zbinom_zero_right, one_mul,
      one_smul]
  have hL2 : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ t * zbinom k n t) •
        Ψ (n - (t : ℤ)) (v + (t : ℤ) + 1) w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k n t) •
        Ψ (n - (t : ℤ)) (v + (t : ℤ) + 1) w := by
    rw [Finset.sum_range_succ, hB (n - (N : ℤ)) (v + (N : ℤ) + 1) (by omega), smul_zero, add_zero]
  rw [hL1, hL2, hR, Finset.sum_sub_distrib]
  abel

theorem eMinus_d12 {Ψ : ℤ → ℤ → ℤ → W} (h : Ψ ∈ T1 k W) (n v w : ℤ) :
    eMinus k n (d12 k W Ψ) v w = eMinus k (n + 1) Ψ v w := by
  obtain ⟨B, hB⟩ := mem_T1.1 h w
  obtain ⟨N₁, h₁⟩ := eMinus_eq_sum (d12_mem_T1 h) n v w
  obtain ⟨N₂, h₂⟩ := eMinus_eq_sum h (n + 1) v w
  obtain ⟨N, hN1, hN2, hNB⟩ : ∃ N : ℕ, N₁ ≤ N ∧ N₂ ≤ N ∧ B ≤ N :=
    ⟨N₁ + N₂ + B.toNat, by omega, by omega, by omega⟩
  rw [h₁ (N + 1) (by omega), h₂ (N + 1) (by omega)]
  simp only [d12_apply, smul_sub, Finset.sum_sub_distrib]
  have hs : (-1 : k) ^ (n + 1) = -(-1 : k) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : k) ≠ 0)]
    ring
  have key : ∀ t ∈ Finset.range N,
      ((-1 : k) ^ (n + 1) * ((-1 : k) ^ (t + 1) * zbinom k (n + 1) (t + 1))) •
          Ψ ((t + 1 : ℕ) : ℤ) (n + 1 + v - ((t + 1 : ℕ) : ℤ)) w =
        ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) • Ψ ((t : ℤ) + 1) (n + v - t) w -
          ((-1 : k) ^ n * ((-1 : k) ^ (t + 1) * zbinom k n (t + 1))) •
            Ψ ((t + 1 : ℕ) : ℤ) (n + v - ((t + 1 : ℕ) : ℤ) + 1) w := by
    intro t _
    have e1 : n + 1 + v - ((t + 1 : ℕ) : ℤ) = n + v - t := by push_cast; ring
    have e2 : n + v - ((t + 1 : ℕ) : ℤ) + 1 = n + v - t := by push_cast; ring
    have e3 : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
    rw [e1, e2, e3, zbinom_succ_succ, hs, pow_succ]
    module
  have hR : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ (n + 1) * ((-1 : k) ^ t *
        zbinom k (n + 1) t)) • Ψ (t : ℤ) (n + 1 + v - t) w =
      ∑ t ∈ Finset.range N, (((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) •
            Ψ ((t : ℤ) + 1) (n + v - t) w -
          ((-1 : k) ^ n * ((-1 : k) ^ (t + 1) * zbinom k n (t + 1))) •
            Ψ ((t + 1 : ℕ) : ℤ) (n + v - ((t + 1 : ℕ) : ℤ) + 1) w) -
        (-1 : k) ^ n • Ψ 0 (n + 1 + v) w := by
    rw [Finset.sum_range_succ', Finset.sum_congr rfl key, hs]
    simp only [Nat.cast_zero, sub_zero, pow_zero, zbinom_zero_right, mul_one, neg_smul]
    abel
  have hL1 : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) •
        Ψ ((t : ℤ) + 1) (n + v - t) w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) •
        Ψ ((t : ℤ) + 1) (n + v - t) w := by
    rw [Finset.sum_range_succ, hB ((N : ℤ) + 1) (n + v - N) (by omega), smul_zero, add_zero]
  have hL2 : ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ n * ((-1 : k) ^ t * zbinom k n t)) •
        Ψ (t : ℤ) (n + v - t + 1) w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ n * ((-1 : k) ^ (t + 1) * zbinom k n (t + 1))) •
          Ψ ((t + 1 : ℕ) : ℤ) (n + v - ((t + 1 : ℕ) : ℤ) + 1) w +
        (-1 : k) ^ n • Ψ 0 (n + 1 + v) w := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, sub_zero, pow_zero, zbinom_zero_right, mul_one]
    rw [show n + v + 1 = n + 1 + v by ring]
  rw [hL1, hL2, hR, Finset.sum_sub_distrib]
  abel

theorem ePlus_d12_pow (j : ℕ) :
    ∀ {Ψ : ℤ → ℤ → ℤ → W}, Ψ ∈ T2 k W → ∀ n v w,
      ePlus k n (((d12 k W) ^ j) Ψ) v w = ePlus k (n + j) Ψ v w := by
  induction j with
  | zero => intro Ψ _ n v w; rw [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]
  | succ j ih =>
    intro Ψ h n v w
    rw [pow_succ, Module.End.mul_apply, ih (d12_mem_T2 h), ePlus_d12 h]
    push_cast
    ring_nf

theorem eMinus_d12_pow (j : ℕ) :
    ∀ {Ψ : ℤ → ℤ → ℤ → W}, Ψ ∈ T1 k W → ∀ n v w,
      eMinus k n (((d12 k W) ^ j) Ψ) v w = eMinus k (n + j) Ψ v w := by
  induction j with
  | zero => intro Ψ _ n v w; rw [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]
  | succ j ih =>
    intro Ψ h n v w
    rw [pow_succ, Module.End.mul_apply, ih (d12_mem_T1 h), eMinus_d12 h]
    push_cast
    ring_nf

/-! ### For `n ≥ 0` both expansions are the polynomial `(z₁ - z₂)^n` -/

theorem ePlus_natCast (Ψ : ℤ → ℤ → ℤ → W) (N : ℕ) (v w : ℤ) :
    ePlus k N Ψ v w = ((d12 k W) ^ N) Ψ 0 v w := by
  rw [d12_pow_apply]
  unfold ePlus dz
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [zbinom_natCast, zero_add]
  · intro t ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact ht (by dsimp only; rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul])

theorem eMinus_natCast (Ψ : ℤ → ℤ → ℤ → W) (N : ℕ) (v w : ℤ) :
    eMinus k N Ψ v w = ((d12 k W) ^ N) Ψ 0 v w := by
  rw [d12_pow_apply]
  have hs : dz k N (fun u v' => Ψ v' u w) v 0 =
      (-1 : k) ^ N • dz k N (fun p q => Ψ p q w) 0 v := dz_swap k N (fun p q => Ψ p q w) 0 v
  have h2 : dz k N (fun p q => Ψ p q w) 0 v = (-1 : k) ^ N • dz k N (fun u v' => Ψ v' u w) v 0 := by
    rw [hs, smul_smul, neg_one_pow_mul_self, one_smul]
  rw [h2]
  unfold eMinus dz
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_, Finset.smul_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [zbinom_natCast, zpow_natCast, smul_smul]
    rw [show (0 : ℤ) + (t : ℤ) = t by ring, show (N : ℤ) + v - (t : ℤ) = v + N - t by ring]
  · intro t ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact ht (by dsimp only; rw [zbinom_natCast_of_lt k (by omega), mul_zero, mul_zero, zero_smul])

/-! ### Dong's lemma, all `n` -/

theorem comm_apply {M' : Type*} [AddCommGroup M'] [Module k M'] {f g : Module.End k M'}
    (h : Commute f g) (x : M') : f (g x) = g (f x) := by
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]

/-- One term of the binomial expansion in Dong's lemma. -/
theorem dong_term (r L s : ℕ) (n : ℤ) (hn : 2 * (r : ℤ) ≤ n + L) (hsL : s ≤ L)
    (Φp Φm : ℤ → ℤ → ℤ → W) (hp : Φp ∈ T2 k W) (hm : Φm ∈ T1 k W)
    (h12 : ((d12 k W) ^ r) (Φp - Φm) = 0)
    (h3p : ((d13 k W) ^ r) (((d23 k W) ^ r) Φp) = 0)
    (h3m : ((d13 k W) ^ r) (((d23 k W) ^ r) Φm) = 0) (v w : ℤ) :
    ePlus k n (((d13 k W) ^ s) (((d12 k W) ^ (L - s)) (((d23 k W) ^ r) Φp))) v w -
      eMinus k n (((d13 k W) ^ s) (((d12 k W) ^ (L - s)) (((d23 k W) ^ r) Φm))) v w = 0 := by
  have h1 : Commute ((d13 k W) ^ s) ((d12 k W) ^ (L - s)) :=
    (commute_d13_d12 (k := k) (W := W)).pow_pow s (L - s)
  rw [comm_apply h1, comm_apply h1]
  by_cases hs : r ≤ s
  · rw [pow_apply_eq_zero_of_le h3p hs, pow_apply_eq_zero_of_le h3m hs, map_zero,
      ePlus_zero, eMinus_zero, sub_zero]
  · replace hs : s < r := by omega
    have hpΨ : ((d23 k W) ^ r) Φp ∈ T2 k W := d23_pow_mem_T2 r hp
    have hmΨ : ((d23 k W) ^ r) Φm ∈ T1 k W := d23_pow_mem_T1 r hm
    have hXp := d13_pow_mem_T2 s hpΨ
    have hXm := d13_pow_mem_T1 s hmΨ
    rw [ePlus_d12_pow (L - s) hXp, eMinus_d12_pow (L - s) hXm]
    obtain ⟨N', hN'1, hN'2⟩ : ∃ N' : ℕ, n + ((L - s : ℕ) : ℤ) = (N' : ℤ) ∧ r ≤ N' :=
      ⟨(n + ((L - s : ℕ) : ℤ)).toNat, by omega, by omega⟩
    rw [hN'1, ePlus_natCast, eMinus_natCast]
    have hsub : ((d12 k W) ^ N') (((d13 k W) ^ s) (((d23 k W) ^ r) Φp)) 0 v w -
        ((d12 k W) ^ N') (((d13 k W) ^ s) (((d23 k W) ^ r) Φm)) 0 v w =
        ((d12 k W) ^ N') (((d13 k W) ^ s) (((d23 k W) ^ r) (Φp - Φm))) 0 v w := by
      rw [map_sub, map_sub, map_sub]
      rfl
    have c1 : Commute ((d12 k W) ^ N') ((d13 k W) ^ s) :=
      ((commute_d13_d12 (k := k) (W := W)).pow_pow s N').symm
    have c2 : Commute ((d12 k W) ^ N') ((d23 k W) ^ r) :=
      ((commute_d23_d12 (k := k) (W := W)).pow_pow r N').symm
    rw [hsub, comm_apply c1, comm_apply c2, pow_apply_eq_zero_of_le h12 hN'2, map_zero, map_zero]
    rfl

/-- **Dong's lemma, abstract form, all `n`.** -/
theorem dong_general (r L : ℕ) (n : ℤ) (hn : 2 * (r : ℤ) ≤ n + L)
    (Φp Φm : ℤ → ℤ → ℤ → W) (hp : Φp ∈ T2 k W) (hm : Φm ∈ T1 k W)
    (h12 : ((d12 k W) ^ r) (Φp - Φm) = 0)
    (h3p : ((d13 k W) ^ r) (((d23 k W) ^ r) Φp) = 0)
    (h3m : ((d13 k W) ^ r) (((d23 k W) ^ r) Φm) = 0) (v w : ℤ) :
    dz k (L + r) (fun v w => ePlus k n Φp v w - eMinus k n Φm v w) v w = 0 := by
  have hpΨ : ((d23 k W) ^ r) Φp ∈ T2 k W := d23_pow_mem_T2 r hp
  have hmΨ : ((d23 k W) ^ r) Φm ∈ T1 k W := d23_pow_mem_T1 r hm
  have hexp : (d23 k W) ^ L = ∑ s ∈ Finset.range (L + 1),
      (d13 k W) ^ s * (-d12 k W) ^ (L - s) * (L.choose s : Module.End k (ℤ → ℤ → ℤ → W)) := by
    rw [d23_eq]
    exact ((commute_d13_d12 (k := k) (W := W)).neg_right).add_pow _
  have hterm : ∀ (s : ℕ) (Ψ : ℤ → ℤ → ℤ → W),
      ((d13 k W) ^ s * (-d12 k W) ^ (L - s) * (L.choose s : Module.End k (ℤ → ℤ → ℤ → W))) Ψ =
        ((L.choose s : k) * (-1 : k) ^ (L - s)) • ((d13 k W) ^ s) (((d12 k W) ^ (L - s)) Ψ) := by
    intro s Ψ
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
      map_nsmul, neg_pow_apply, map_smul, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  have hsum : ∀ Ψ : ℤ → ℤ → ℤ → W, ((d23 k W) ^ L) Ψ = ∑ s ∈ Finset.range (L + 1),
      ((L.choose s : k) * (-1 : k) ^ (L - s)) • ((d13 k W) ^ s) (((d12 k W) ^ (L - s)) Ψ) := by
    intro Ψ
    rw [hexp, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun s _ => hterm s Ψ
  have hmemP : ∀ s ∈ Finset.range (L + 1),
      ((L.choose s : k) * (-1 : k) ^ (L - s)) • ((d13 k W) ^ s) (((d12 k W) ^ (L - s))
        (((d23 k W) ^ r) Φp)) ∈ T2 k W := fun s _ =>
    Submodule.smul_mem _ _ (d13_pow_mem_T2 s (d12_pow_mem_T2 _ hpΨ))
  have hmemM : ∀ s ∈ Finset.range (L + 1),
      ((L.choose s : k) * (-1 : k) ^ (L - s)) • ((d13 k W) ^ s) (((d12 k W) ^ (L - s))
        (((d23 k W) ^ r) Φm)) ∈ T1 k W := fun s _ =>
    Submodule.smul_mem _ _ (d13_pow_mem_T1 s (d12_pow_mem_T1 _ hmΨ))
  rw [dz_sub_fun, ← ePlus_d23_pow hp n (L + r) v w, ← eMinus_d23_pow hm n (L + r) v w, pow_add,
    Module.End.mul_apply, Module.End.mul_apply, hsum, hsum,
    ePlus_sum _ _ hmemP, eMinus_sum _ _ hmemM, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun s hsL => ?_
  have hsL' : s ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hsL)
  rw [ePlus_smul (d13_pow_mem_T2 s (d12_pow_mem_T2 _ hpΨ)),
    eMinus_smul (d13_pow_mem_T1 s (d12_pow_mem_T1 _ hmΨ)), ← smul_sub,
    dong_term r L s n hn hsL' Φp Φm hp hm h12 h3p h3m v w, smul_zero]

end Expansions

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ePlus_d12_pow
#print axioms HaagerupIzumi.C8.eMinus_d12_pow
#print axioms HaagerupIzumi.C8.ePlus_natCast
#print axioms HaagerupIzumi.C8.eMinus_natCast
#print axioms HaagerupIzumi.C8.dong_general
