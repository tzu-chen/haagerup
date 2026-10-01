module

public import HaagerupIzumi.C8.MainProperness

@[expose] public section

/-!
# Nilpotence of raising words from bounded Cartan charges (Lemma `lem:current-bounds`)

`prop_mainproper` uses the hypotheses `hnilE`, `hnilF`: every word of length `25` in the two
raising (resp. lowering) current zero modes vanishes on `S₃`.  The manuscript derives this
(lines 2289–2295): "At weight three Lemma `lem:current-bounds` bounds the two Cartan eigenvalues
by `|m_L| ≤ 3` and `|m_R| ≤ 21`.  Either raising operator increases `m_L + m_R` by two.  Every
word of length `25` in the two raising operators therefore vanishes."

`raisingWord_zero_of_charge` proves this implication: if `v` lies in the span of the charge
spaces `gr k` (eigenspaces of `H_L(0) + H_R(0)`, say), these vanish for `|k| > 24`, and the two
operators raise the charge by two, then every word of length `25` kills `v`.
`prop_mainproper_of_charges` restates `prop_mainproper` with these more primitive inputs.  The
intended `gr c` are the charge spaces *inside the weight-three space* `B₃` (on all of `B` the
charges are unbounded); only `S₃ ≤ ⨆ gr c` and the bounds on these spaces are used.
The bound `|m_L| + |m_R| ≤ 24` on `B₃` is the lattice estimate of Lemma `lem:current-bounds`
(`HaagerupIzumi.C8.totalWeight_bound_three` in `Sl2/CurrentBounds.lean` proves the arithmetic);
that the charge spaces span `S₃` is the diagonal Cartan action on Fock monomials.
-/

namespace HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]

open HaagerupIzumi.CFT

/-- A word of length `n` in two operators raising a `ℤ`-grading by two raises it by `2n`. -/
theorem raisingWord_mem_charge (gr : ℤ → Submodule k V) (E F : V →ₗ[k] V)
    (hE : ∀ c, ∀ x ∈ gr c, E x ∈ gr (c + 2)) (hF : ∀ c, ∀ x ∈ gr c, F x ∈ gr (c + 2)) :
    ∀ (w : List Bool) (c : ℤ) (x : V), x ∈ gr c →
      raisingWord E F w x ∈ gr (c + 2 * (w.length : ℤ)) := by
  intro w
  induction w with
  | nil =>
    intro c x hx
    simpa [raisingWord] using hx
  | cons b w ih =>
    intro c x hx
    have hw := ih c x hx
    have e : c + 2 * ((b :: w).length : ℤ) = (c + 2 * (w.length : ℤ)) + 2 := by
      simp only [List.length_cons]; push_cast; ring
    rw [e]
    cases b with
    | false => exact hF _ _ hw
    | true => exact hE _ _ hw

/-- **Bounded charge ⇒ nilpotent raising words.**  If `v` lies in the span of the charge spaces,
these vanish outside `[-24, 24]`, and `E, F` raise the charge by two, then every word of
length `25` in `E, F` kills `v`. -/
theorem raisingWord_zero_of_charge (gr : ℤ → Submodule k V)
    (hsupp : ∀ c : ℤ, (c < -24 ∨ 24 < c) → gr c = ⊥) (E F : V →ₗ[k] V)
    (hE : ∀ c, ∀ x ∈ gr c, E x ∈ gr (c + 2)) (hF : ∀ c, ∀ x ∈ gr c, F x ∈ gr (c + 2))
    (w : List Bool) (hw : w.length = 25) {v : V} (hv : v ∈ ⨆ c, gr c) :
    raisingWord E F w v = 0 := by
  refine Submodule.iSup_induction gr (motive := fun x => raisingWord E F w x = 0) hv ?_ ?_ ?_
  · intro c x hx
    by_cases hc : c < -24
    · rw [hsupp c (Or.inl hc)] at hx
      rw [(Submodule.mem_bot k).mp hx, map_zero]
    · have h1 := raisingWord_mem_charge gr E F hE hF w c x hx
      rw [hw, hsupp (c + 2 * ((25 : ℕ) : ℤ)) (Or.inr (by push_cast; omega))] at h1
      exact (Submodule.mem_bot k).mp h1
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

variable {A : VertexOperatorAlgebra k V}

/-- **Proposition `prop:mainproper` from bounded Cartan charges.**  As `prop_mainproper`, with
the nilpotence of raising/lowering words replaced by: `S₃` lies in the span of charge spaces
`gr c` vanishing for `|c| > 24`, the raising zero modes raise the charge by two and the
lowering zero modes lower it by two. -/
theorem prop_mainproper_of_charges (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (gr : ℤ → Submodule k V) (hsupp : ∀ c : ℤ, (c < -24 ∨ 24 < c) → gr c = ⊥)
    (hS₃ : D.S₃ ≤ ⨆ c, gr c)
    (hEL : ∀ c, ∀ x ∈ gr c, A.mode 0 D.eL x ∈ gr (c + 2))
    (hER : ∀ c, ∀ x ∈ gr c, A.mode 0 D.eR x ∈ gr (c + 2))
    (hFL : ∀ c, ∀ x ∈ gr c, A.mode 0 D.fL x ∈ gr (c - 2))
    (hFR : ∀ c, ∀ x ∈ gr c, A.mode 0 D.fR x ∈ gr (c - 2))
    (u : V) (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u) :
    D.U u = A.normalSpan (⋃ d, (D.family d : Set V)) ∧ D.U u ⊓ A.grade 1 = D.K := by
  -- the lowering operators raise the reflected grading `c ↦ gr (-c)` by two
  set gr' : ℤ → Submodule k V := fun c => gr (-c)
  have hsupp' : ∀ c : ℤ, (c < -24 ∨ 24 < c) → gr' c = ⊥ := fun c hc =>
    hsupp (-c) (by omega)
  have hS₃' : D.S₃ ≤ ⨆ c, gr' c := by
    refine hS₃.trans (iSup_le fun c => ?_)
    have : gr c = gr' (-c) := by simp [gr']
    rw [this]
    exact le_iSup gr' (-c)
  have hFL' : ∀ c, ∀ x ∈ gr' c, A.mode 0 D.fL x ∈ gr' (c + 2) := fun c x hx => by
    have := hFL (-c) x hx
    simpa [gr', show -(c + 2) = -c - 2 by ring] using this
  have hFR' : ∀ c, ∀ x ∈ gr' c, A.mode 0 D.fR x ∈ gr' (c + 2) := fun c x hx => by
    have := hFR (-c) x hx
    simpa [gr', show -(c + 2) = -c - 2 by ring] using this
  refine prop_mainproper D L G G5 ?_ ?_ u hω hu hmin
  · exact fun w hw v hv => raisingWord_zero_of_charge gr hsupp _ _ hEL hER w hw (hS₃ hv)
  · exact fun w hw v hv => raisingWord_zero_of_charge gr' hsupp' _ _ hFL' hFR' w hw (hS₃' hv)

#print axioms prop_mainproper_of_charges

end HaagerupIzumi.C8
