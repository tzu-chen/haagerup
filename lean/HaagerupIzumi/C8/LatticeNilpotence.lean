module

public import HaagerupIzumi.C8.Nilpotence
public import HaagerupIzumi.C8.Sl2.CurrentBounds

@[expose] public section

/-!
# Nilpotence of raising words from the lattice (Lemma `lem:current-bounds`)

`prop_mainproper_of_charges` needs charge spaces `gr c ⊇ S₃`, vanishing for `|c| > 24`, raised
by two by the raising current zero modes.  Here they are built from the lattice: the weight-three
space of `B = V_{E₆⊕A₂}` is the sum of its Fock components `fock α` of momentum `α` with
`(α,α)/2 ≤ 3`; the total Cartan charge of `fock α` is `charge α = (α_L + h_R, α)`; and the
zero modes of `E_L = e^{α_L}` and `E_R = ∑_{c_i ≠ 0} e^{α_i}` shift momenta by `α_L` and `α_i`,
both of charge `2` (`Lattice.alphaL_norm`, `alphaL_hR`, `alphaL_orthogonal`, `hR_pairing`).  The
bound `|charge α| ≤ 24` for `(α,α) ≤ 6` is `Sl2.totalWeight_bound_three` (Cauchy–Schwarz in
the positive-definite lattice), exactly the manuscript's estimate `|m_L| ≤ 3`, `|m_R| ≤ 21`.

`prop_mainproper_of_lattice` is Proposition `prop:mainproper` with the nilpotence hypotheses
replaced by these lattice-VOA facts (the Fock decomposition and the momentum shifts of vertex
operators `e^β_(0)`, FLM).
-/

namespace HaagerupIzumi.C8.LatticeNilpotence

open _root_.HaagerupIzumi.C8.Lattice HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The total Cartan charge `m_L + m_R = (α_L, α) + (h_R, α)` of a momentum. -/
def charge (α : Fin 8 → ℤ) : ℤ := form alphaL α + form hR α

theorem charge_add (α β : Fin 8 → ℤ) : charge (α + β) = charge α + charge β := by
  unfold charge
  rw [form_add_right, form_add_right]
  ring

theorem charge_neg (α : Fin 8 → ℤ) : charge (-α) = -charge α := by
  unfold charge
  rw [form_neg_right, form_neg_right]
  ring

theorem charge_alphaL : charge alphaL = 2 := by
  unfold charge
  rw [alphaL_norm, form_comm hR alphaL, alphaL_hR]
  norm_num

theorem charge_simpleRoot (i : Fin 8) (hi : coeffR i ≠ 0) : charge (simpleRoot i) = 2 := by
  unfold charge
  rw [alphaL_orthogonal i hi, hR_pairing i hi]
  norm_num

/-- The charge spaces of the weight-three Fock decomposition. -/
def chargeSpace (fock : (Fin 8 → ℤ) → Submodule k V) (c : ℤ) : Submodule k V :=
  ⨆ (α : Fin 8 → ℤ) (_ : form α α ≤ 6 ∧ charge α = c), fock α

theorem chargeSpace_bot (fock : (Fin 8 → ℤ) → Submodule k V) (c : ℤ)
    (hc : c < -24 ∨ 24 < c) : chargeSpace fock c = ⊥ := by
  unfold chargeSpace
  refine iSup_eq_bot.2 fun α => iSup_eq_bot.2 fun h => ?_
  exfalso
  have hb := Sl2.totalWeight_bound_three α (by linarith [h.1])
  rw [abs_le] at hb
  have hc' := h.2
  unfold charge at hc'
  omega

/-- A Fock component of charge `c'` lies in the charge space `c'` (components of norm `> 6`
vanish at weight three). -/
theorem fock_le_chargeSpace (fock : (Fin 8 → ℤ) → Submodule k V)
    (hnorm : ∀ β, 6 < form β β → fock β = ⊥) (β : Fin 8 → ℤ) :
    fock β ≤ chargeSpace fock (charge β) := by
  by_cases hn : form β β ≤ 6
  · exact le_iSup₂ (f := fun (γ : Fin 8 → ℤ) (_ : form γ γ ≤ 6 ∧ charge γ = charge β) => fock γ)
      β ⟨hn, rfl⟩
  · rw [hnorm β (by omega)]
    exact bot_le

/-- An operator sending each `fock α` into the span of the shifted components `fock (α + δ)`,
`δ ∈ S`, all shifts of charge `t`, maps the charge space `c` into the charge space `c + t`. -/
theorem map_chargeSpace (fock : (Fin 8 → ℤ) → Submodule k V)
    (hnorm : ∀ β, 6 < form β β → fock β = ⊥) (E : V →ₗ[k] V) (S : Set (Fin 8 → ℤ)) (t : ℤ)
    (hS : ∀ δ ∈ S, charge δ = t) (hE : ∀ α, ∀ x ∈ fock α, E x ∈ ⨆ δ ∈ S, fock (α + δ)) (c : ℤ) :
    ∀ x ∈ chargeSpace fock c, E x ∈ chargeSpace fock (c + t) := by
  intro x hx
  unfold chargeSpace at hx
  refine Submodule.iSup_induction _ (motive := fun x => E x ∈ chargeSpace fock (c + t)) hx
    ?_ ?_ ?_
  · intro α y hy
    refine Submodule.iSup_induction _ (motive := fun y => E y ∈ chargeSpace fock (c + t)) hy
      ?_ ?_ ?_
    · intro h z hz
      have hz' := hE α z hz
      have hle : (⨆ δ ∈ S, fock (α + δ)) ≤ chargeSpace fock (c + t) := by
        refine iSup₂_le fun δ hδ => ?_
        have hch : charge (α + δ) = c + t := by rw [charge_add, h.2, hS δ hδ]
        rw [← hch]
        exact fock_le_chargeSpace fock hnorm (α + δ)
      exact hle hz'
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

theorem iSup_fock_le (fock : (Fin 8 → ℤ) → Submodule k V)
    (hnorm : ∀ β, 6 < form β β → fock β = ⊥) :
    (⨆ α, fock α) ≤ ⨆ c, chargeSpace fock c :=
  iSup_le fun α => (fock_le_chargeSpace fock hnorm α).trans (le_iSup (chargeSpace fock) _)

variable {A : VertexOperatorAlgebra k V}

/-- **Proposition `prop:mainproper` from the lattice.**  As `prop_mainproper`, with the
nilpotence of raising and lowering words derived from: the weight-three Fock decomposition
(`S₃ ≤ ⨆ fock α`, components of momentum norm `> 6` vanish), and the momentum shifts of the
current zero modes (`E_L`: `+α_L`; `E_R`: `+α_i`, `c_i ≠ 0`; `F_L`: `-α_L`; `F_R`: `-α_i`). -/
theorem prop_mainproper_of_lattice (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (fock : (Fin 8 → ℤ) → Submodule k V) (hnorm : ∀ β, 6 < form β β → fock β = ⊥)
    (hS₃ : D.S₃ ≤ ⨆ α, fock α)
    (hEL : ∀ α, ∀ x ∈ fock α, A.mode 0 D.eL x ∈ ⨆ δ ∈ ({alphaL} : Set (Fin 8 → ℤ)), fock (α + δ))
    (hER : ∀ α, ∀ x ∈ fock α, A.mode 0 D.eR x ∈
      ⨆ δ ∈ {δ | ∃ i, coeffR i ≠ 0 ∧ δ = simpleRoot i}, fock (α + δ))
    (hFL : ∀ α, ∀ x ∈ fock α,
      A.mode 0 D.fL x ∈ ⨆ δ ∈ ({-alphaL} : Set (Fin 8 → ℤ)), fock (α + δ))
    (hFR : ∀ α, ∀ x ∈ fock α, A.mode 0 D.fR x ∈
      ⨆ δ ∈ {δ | ∃ i, coeffR i ≠ 0 ∧ δ = -simpleRoot i}, fock (α + δ))
    (u : V) (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u) :
    D.U u = A.normalSpan (⋃ d, (D.family d : Set V)) ∧ D.U u ⊓ A.grade 1 = D.K := by
  refine prop_mainproper_of_charges D L G G5 (chargeSpace fock)
    (chargeSpace_bot fock) ((hS₃.trans (iSup_fock_le fock hnorm)))
    (map_chargeSpace fock hnorm _ _ 2 (by rintro δ rfl; exact charge_alphaL) hEL)
    (map_chargeSpace fock hnorm _ _ 2
      (by rintro δ ⟨i, hi, rfl⟩; exact charge_simpleRoot i hi) hER)
    (fun c x hx => by
      have h := map_chargeSpace fock hnorm _ _ (-2)
        (by rintro δ rfl; rw [charge_neg, charge_alphaL]) hFL c x hx
      simpa [sub_eq_add_neg] using h)
    (fun c x hx => by
      have h := map_chargeSpace fock hnorm _ _ (-2)
        (by rintro δ ⟨i, hi, rfl⟩; rw [charge_neg, charge_simpleRoot i hi]) hFR c x hx
      simpa [sub_eq_add_neg] using h)
    u hω hu hmin

#print axioms prop_mainproper_of_lattice

end HaagerupIzumi.C8.LatticeNilpotence
