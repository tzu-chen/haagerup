module

public import HaagerupIzumi.C8.Lattice.Semantic
public import HaagerupIzumi.C8.Lattice.Data

@[expose] public section

/-!
# Grade-two identities: the current algebra `A₁,₁ ⊗ A₁,₃₉` and `L(0)`, `L(-1)` on currents

Work item W1, step 5 (`C8/ROADMAP.md`): identities of the type checked by the unitary
certificate, proved for the Fock model by kernel evaluation (`decide +kernel`) of the
computable modes (`Lattice/Modes.lean`) and transported to `Fock` by `Y_eq_of_mode_eq`.

* `left_sl2`, `right_sl2`: the modes `a_(n) b`, `n = 0, 1`, for one order of each pair of
  currents of `eq:leftcurrents`, `eq:rightcurrents` (lines 1910–1930 of
  `c8_expanded_20260929/haagerup_c8_expanded.tex`): `h₀e = 2e`, `h₀f = -2f`, `e₀f = h`,
  `h₁h = 2k𝟏`, `e₁f = k𝟏`, `h₀h = e₀e = f₀f = h₁e = h₁f = e₁e = f₁f = 0`, with levels `k = 1`
  (left) and `k = 39` (right); modes `n ≥ 2` vanish by grading.  The opposite orders
  (`e_(n)h`, `f_(n)h`, `f_(n)e`) are not kernel-checked here (they follow by skew symmetry once
  the Borcherds identity is available, `Lattice/VOA.lean`).  These upgrade the scalar statements
  `Lattice.leftCurrent_doublePole`, `Lattice.rightCurrent_doublePole` of Lemma `lem:levels`
  (line 1929) to identities of vectors.
* `left_right_commute`: `x_(n) y = 0` for `n = 0, 1`, every left current `x` and every right
  current `y` (this order only).
* `omega_on_currents`: the conformal vector `ω` acts on `e^{α_L}` and `h₀(-1)𝟏` with
  `L(0) = ω_(1)` equal to the grade `1`, `L(1) = ω_(2)` zero, and `L(-1) = ω_(0)` the
  translation `T e^α = α(-1) e^α`.

No hypotheses.  Kernel times are printed by `set_option profiler true`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 20
set_option Elab.async false

/-! ## The left current algebra `A₁,₁` -/

theorem left_sl2 :
    mode hL 0 eL = smul 2 eL ∧ mode hL 0 fL = smul (-2) fL ∧ mode eL 0 fL = hL ∧
    mode hL 0 hL = [] ∧ mode eL 0 eL = [] ∧ mode fL 0 fL = [] ∧
    mode hL 1 hL = smul 2 vac ∧ mode eL 1 fL = vac ∧ mode hL 1 eL = [] ∧ mode hL 1 fL = [] ∧
    mode eL 1 eL = [] ∧ mode fL 1 fL = [] := by
  decide +kernel

/-! ## The right current algebra `A₁,₃₉` -/

theorem right_sl2 :
    mode hR 0 eR = smul 2 eR ∧ mode hR 0 fR = smul (-2) fR ∧ mode eR 0 fR = hR ∧
    mode hR 0 hR = [] ∧ mode eR 0 eR = [] ∧ mode fR 0 fR = [] ∧
    mode hR 1 hR = smul 78 vac ∧ mode eR 1 fR = smul 39 vac ∧ mode hR 1 eR = [] ∧
    mode hR 1 fR = [] ∧ mode eR 1 eR = [] ∧ mode fR 1 fR = [] := by
  decide +kernel

/-! ## The two current algebras commute -/

theorem left_right_commute :
    ∀ x ∈ [hL, eL, fL], ∀ y ∈ [hR, eR, fR], mode x 0 y = [] ∧ mode x 1 y = [] := by
  decide +kernel

/-! ## The conformal vector on weight-one states -/

theorem omega_on_currents :
    mode omega 1 eL = eL ∧ mode omega 2 eL = [] ∧
    mode omega 0 eL =
      [(S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [0], -1), (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [1], -2),
        (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [2], -3), (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [3], -2),
        (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [4], -1), (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [5], -2)] ∧
    mode omega 1 [(S 0 0 0 0 0 0 0 0 [0], 1)] = [(S 0 0 0 0 0 0 0 0 [0], 1)] ∧
    mode omega 2 [(S 0 0 0 0 0 0 0 0 [0], 1)] = [] ∧
    mode omega 0 [(S 0 0 0 0 0 0 0 0 [0], 1)] = [(S 0 0 0 0 0 0 0 0 [8], 1)] := by
  decide +kernel

/-! ## Semantic forms -/

/-- The left `sl₂` relations as identities of modes on the Fock model. -/
theorem left_sl2_Y :
    Y (toFock hL) 0 (toFock eL) = (2 : ℚ) • toFock eL ∧
    Y (toFock eL) 0 (toFock fL) = toFock hL ∧
    Y (toFock hL) 1 (toFock hL) = (2 : ℚ) • toFock vac ∧
    Y (toFock eL) 1 (toFock fL) = toFock vac := by
  obtain ⟨h1, -, h3, -, -, -, h7, h8, -⟩ := left_sl2
  refine ⟨?_, Y_eq_of_mode_eq h3, ?_, Y_eq_of_mode_eq h8⟩
  · rw [Y_eq_of_mode_eq h1, toFock_smul]
  · rw [Y_eq_of_mode_eq h7, toFock_smul]

/-- The right `sl₂` relations (level `39`) as identities of modes on the Fock model. -/
theorem right_sl2_Y :
    Y (toFock hR) 0 (toFock eR) = (2 : ℚ) • toFock eR ∧
    Y (toFock eR) 0 (toFock fR) = toFock hR ∧
    Y (toFock hR) 1 (toFock hR) = (78 : ℚ) • toFock vac ∧
    Y (toFock eR) 1 (toFock fR) = (39 : ℚ) • toFock vac := by
  obtain ⟨h1, -, h3, -, -, -, h7, h8, -⟩ := right_sl2
  refine ⟨?_, Y_eq_of_mode_eq h3, ?_, ?_⟩
  · rw [Y_eq_of_mode_eq h1, toFock_smul]
  · rw [Y_eq_of_mode_eq h7, toFock_smul]
  · rw [Y_eq_of_mode_eq h8, toFock_smul]

#print axioms left_sl2
#print axioms right_sl2
#print axioms left_right_commute
#print axioms omega_on_currents
#print axioms left_sl2_Y
#print axioms right_sl2_Y

end LatticeVOA
end HaagerupIzumi.C8
