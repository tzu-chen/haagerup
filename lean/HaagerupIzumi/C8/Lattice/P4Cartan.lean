module

public import HaagerupIzumi.C8.Lattice.FLMGen

@[expose] public section

/-!
# Cartan zero modes act diagonally on the Fock model

For the triplet controls (`hi_cft_20260923_next_structure_p4_controls.json`): the zero mode of a
Cartan current `h = ∑ cᵢ hᵢ(-1)𝟏` acts on a monomial with momentum `β` by the scalar
`∑ cᵢ (αᵢ, β)` (`cartanEig`).  Proved from the definitions of the modes:

* `toFock_basisModeAux_zero`: `(hᵢ(-1)𝟏)_(0) = hᵢ(0)` on monomials;
* `modeC_cartan_single`, `modeC_cartan_toV4`: for a Cartan vector `h` (`IsCartanVec h`, checked
  by `decide` for `hL`, `hR`) and a vector all of whose states have eigenvalue `λ`,
  `h_(0) x = λ x`.

So the Cartan controls of the triplet reduce to a check on the states of the data
(`P4States*.lean`), with no mode computation in the kernel.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- `∑ cᵢ (αᵢ, β)` for `h = ∑ cᵢ hᵢ(-1)𝟏`. -/
def cartanEig (h : Vec) (β : Mom) : ℚ :=
  (h.map fun p => p.2 * (Mom.pairSimple (p.1.2.headD 0) β : ℚ)).sum

/-- `h` is a combination of the `hᵢ(-1)𝟏`, `i < 8`. -/
def IsCartanVec (h : Vec) : Prop := ∀ p ∈ h, ∃ i < 8, p.1 = (Mom.zero, [i])

instance (h : Vec) : Decidable (IsCartanVec h) :=
  inferInstanceAs (Decidable (∀ p ∈ h, ∃ i < 8, p.1 = (Mom.zero, [i])))

theorem hL_cartan : IsCartanVec hL := by decide +kernel
theorem hR_cartan : IsCartanVec hR := by decide +kernel

theorem toFock_foldr_vertex_zero_all (c : ℕ → ℚ) (v : State) (F : ℕ → ℤ) (G : ℕ → State → Vec)
    (hF : ∀ j, F j ≠ -1) (l : List ℕ) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (basisModeAux Mom.zero [] (F j) v) (G j))) acc) []) = 0 := by
  rw [toFock_foldr_addVec]
  refine List.sum_eq_zero fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  rw [toFock_smul, toFock_bindVec,
    show basisModeAux Mom.zero [] (F j) v = vertexOp Mom.zero (F j) v from rfl,
    toFock_vertexOp_zero, if_neg (hF j), map_zero, smul_zero]

theorem linearCombination_single_one (f : Fock) :
    Finsupp.linearCombination ℚ (fun s => Finsupp.single s (1 : ℚ)) f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single a b => rw [Finsupp.linearCombination_single, Finsupp.smul_single_one]

theorem toFock_foldr_bind_vertex_single (c : ℕ → ℚ) (H : ℕ → Vec) (F : ℕ → ℤ) (l : List ℕ)
    (j₀ : ℕ) (hnd : l.Nodup) (hj₀ : j₀ ∈ l) (hF : ∀ j, F j = -1 ↔ j = j₀) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (H j) (basisModeAux Mom.zero [] (F j)))) acc) []) =
      c j₀ • toFock (H j₀) := by
  have hv1 : (fun s => toFock (basisModeAux Mom.zero [] (F j₀) s)) = fun s => Finsupp.single s 1 := by
    funext s
    rw [show basisModeAux Mom.zero [] (F j₀) s = vertexOp Mom.zero (F j₀) s from rfl,
      toFock_vertexOp_zero, if_pos ((hF j₀).2 rfl)]
  have hv0 : ∀ j, j ≠ j₀ → (fun s => toFock (basisModeAux Mom.zero [] (F j) s)) = fun _ => 0 :=
    fun j hj => by
      funext s
      rw [show basisModeAux Mom.zero [] (F j) s = vertexOp Mom.zero (F j) s from rfl,
        toFock_vertexOp_zero, if_neg (fun h => hj ((hF j).1 h))]
  rw [toFock_foldr_addVec, list_sum_map_eq_single _ j₀ l hnd hj₀ ?_]
  · rw [toFock_smul, toFock_bindVec, hv1, linearCombination_single_one]
  · intro j _ hj
    rw [toFock_smul, toFock_bindVec, hv0 j hj]
    simp [Finsupp.linearCombination_apply]

/-- `(hᵢ(-1)𝟏)_(0) = hᵢ(0)` on monomials. -/
theorem toFock_basisModeAux_zero (i : ℕ) (hi : i < 8) (v : State) :
    toFock (basisModeAux Mom.zero [i] 0 v) = toFock (heis i 0 v) := by
  have h1 : i % 8 = i := Nat.mod_eq_of_lt hi
  have h2 : i / 8 = 0 := Nat.div_eq_of_lt hi
  rw [basisModeAux.eq_2]
  simp only [h1, h2]
  rw [toFock_addVec, toFock_foldr_vertex_zero_all _ _ _ _ ?_,
    toFock_foldr_bind_vertex_single _ _ _ _ 0 List.nodup_range ?_ ?_, zero_add]
  · simp [gbinom_zero_right]
  · rw [List.mem_range]
    omega
  · intro j
    constructor <;> intro h <;> omega
  · intro j h
    omega

theorem toFock_heis_zero (i : ℕ) (v : State) :
    toFock (heis i 0 v) = Finsupp.single v (Mom.pairSimple i v.1 : ℚ) := by
  simp [heis, toFock_addTerm]

/-- `(hᵢ(-1)𝟏)_(0)` acts on a canonical monomial `t` by `(αᵢ, β_t)`. -/
theorem modeC_hV_zero (i : ℕ) (hi : i < 8) (t : ValidState) (d : ℂ) :
    modeC 0 (hV i) (Finsupp.single t d) = (Mom.pairSimple i t.1.1 : ℂ) • Finsupp.single t d := by
  rw [hV, modeC_single, one_mul]
  show d • push (toFock (basisModeAux Mom.zero [i] 0 t.1)) = _
  rw [toFock_basisModeAux_zero i hi, toFock_heis_zero, push_single, canon_of_valid t.2,
    Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
  congr 1
  push_cast
  ring

/-- A Cartan vector acts on a canonical monomial by its eigenvalue. -/
theorem modeC_cartan_single :
    ∀ h : Vec, IsCartanVec h → ∀ (t : ValidState) (d : ℂ),
      modeC 0 (toV h) (Finsupp.single t d) = (cartanEig h t.1.1 : ℂ) • Finsupp.single t d
  | [], _, t, d => by simp [cartanEig]
  | (s, c) :: h, hh, t, d => by
    obtain ⟨i, hi, hs⟩ := hh (s, c) List.mem_cons_self
    have ih := modeC_cartan_single h (fun p hp => hh p (List.mem_cons_of_mem _ hp)) t d
    have hc : canon s = hState i := by
      simp only at hs
      rw [hs]
      exact canon_of_valid (s := (Mom.zero, [i])) (List.pairwise_singleton _ _)
    have hsingle : Finsupp.single (hState i) (c : ℂ) = (c : ℂ) • hV i := by
      rw [hV, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only at hs
    rw [toV_cons_mk, hc, hsingle, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      modeC_hV_zero i hi, ih]
    simp only [cartanEig, List.map_cons, List.sum_cons, hs]
    push_cast
    simp only [List.headD_cons]
    module

theorem modeC_cartan_toV (h : Vec) (hh : IsCartanVec h) (μ : ℚ) :
    ∀ v : Vec, (∀ p ∈ v, Valid p.1 ∧ cartanEig h p.1.1 = μ) →
      modeC 0 (toV h) (toV v) = (μ : ℂ) • toV v
  | [], _ => by simp
  | (s, c) :: v, hv => by
    obtain ⟨hsv, hse⟩ := hv (s, c) List.mem_cons_self
    have ih := modeC_cartan_toV h hh μ v fun p hp => hv p (List.mem_cons_of_mem _ hp)
    have e : cartanEig h (⟨s, hsv⟩ : ValidState).1.1 = μ := hse
    rw [toV_cons_mk, map_add, ih, canon_of_valid hsv, modeC_cartan_single h hh, smul_add, e]

/-- **`h_(0) x = μ x`** for a Cartan vector `h` and a vector `x` over `ℚ(√13, √-3)` all of whose
states are canonical with `h`-eigenvalue `μ`. -/
theorem modeC_cartan_toV4 (h : Vec) (hh : IsCartanVec h) (μ : ℚ) (x : Vec4)
    (hx : x.AllStates fun s => Valid s ∧ cartanEig h s.1 = μ) :
    modeC 0 (toV h) (toV4 x) = (μ : ℂ) • toV4 x := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  simp only [toV4, map_add, map_smul, modeC_cartan_toV h hh μ _ h0, modeC_cartan_toV h hh μ _ h1,
    modeC_cartan_toV h hh μ _ h2, modeC_cartan_toV h hh μ _ h3]
  module

#print axioms modeC_cartan_toV4

end LatticeVOA
end HaagerupIzumi.C8
