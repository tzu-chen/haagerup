module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-!
# Linear-algebraic parts of the finite closure argument

This file formalizes three algebraic steps used in the central-charge-eight
manuscript: nilpotent raising saturation, recovery from a projected residual,
and cancellation of a nonzero scalar in the Jacobi gate.

It does not define a vertex algebra, reconstruct lattice fields, authenticate
the numerical certificates, or formalize the filtered Wick argument. In the
saturation theorem, joint nilpotence is an explicit hypothesis. In the
application it follows from the bounded Cartan weights of a finite current
module, and the spanning hypothesis is supplied by the saved rank witness.
-/

namespace HaagerupIzumi.CFT

section Raising

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A word in two raising operators. `true` chooses `E`, and `false`
chooses `F`. The head of the list is the outermost operator. -/
def raisingWord (E F : M →ₗ[R] M) : List Bool → M →ₗ[R] M
  | [] => LinearMap.id
  | b :: w => (if b then E else F).comp (raisingWord E F w)

/-- Concatenation is composition, in the convention used by `raisingWord`. -/
theorem raisingWord_append_apply (E F : M →ₗ[R] M)
    (u v : List Bool) (x : M) :
    raisingWord E F (u ++ v) x =
      raisingWord E F u (raisingWord E F v x) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      change (if b then E else F) (raisingWord E F (u ++ v) x) =
        (if b then E else F) (raisingWord E F u (raisingWord E F v x))
      rw [ih]

/-- Stability under the two operators implies stability under every word. -/
theorem raisingWord_mem (C : Submodule R M) (E F : M →ₗ[R] M)
    (hE : ∀ x ∈ C, E x ∈ C) (hF : ∀ x ∈ C, F x ∈ C)
    (w : List Bool) {x : M} (hx : x ∈ C) :
    raisingWord E F w x ∈ C := by
  induction w with
  | nil => exact hx
  | cons b w ih =>
      cases b with
      | false => exact hF _ ih
      | true => exact hE _ ih

/-- Nilpotent saturation, in a form that needs neither finite-dimensionality
nor commutation as separate hypotheses. Joint nilpotence means that every
word of one fixed length acts as zero. A stable subspace containing a set of
raising coinvariant representatives must then be the whole space. -/
theorem nilpotent_raising_saturation
    (C : Submodule R M) (E F : M →ₗ[R] M)
    (hE : ∀ x ∈ C, E x ∈ C) (hF : ∀ x ∈ C, F x ∈ C)
    (hspan : ∀ v : M, ∃ x y c : M, c ∈ C ∧ v = E x + F y + c)
    (N : ℕ)
    (hnil : ∀ w : List Bool, w.length = N →
      ∀ v : M, raisingWord E F w v = 0) :
    ∀ v : M, v ∈ C := by
  let P : ℕ → Prop := fun n =>
    ∀ w : List Bool, w.length = n → ∀ v : M, raisingWord E F w v ∈ C
  have step : ∀ n : ℕ, P (n + 1) → P n := by
    intro n hn w hw v
    rcases hspan v with ⟨x, y, c, hc, hv⟩
    rw [hv, map_add, map_add]
    apply C.add_mem
    · apply C.add_mem
      · have h := hn (w ++ [true]) (by simp [hw]) x
        simpa [raisingWord_append_apply, raisingWord] using h
      · have h := hn (w ++ [false]) (by simp [hw]) y
        simpa [raisingWord_append_apply, raisingWord] using h
    · exact raisingWord_mem C E F hE hF w hc
  have descend : ∀ n : ℕ, P n → P 0 := by
    intro n
    induction n with
    | zero => exact fun h => h
    | succ n ih => exact fun h => ih (step n h)
  have terminal : P N := by
    intro w hw v
    rw [hnil w hw v]
    exact C.zero_mem
  have initial : P 0 := descend N terminal
  intro v
  exact initial [] rfl v

/-- The quotient argument in singlet recovery: a projected vector in the
normal space recovers the original vector if the projection is the identity
modulo that space. Idempotence of the operator is unnecessary. -/
theorem projected_residual_recovery
    (C : Submodule R M) (P : M →ₗ[R] M) (v : M)
    (hquotient : v - P v ∈ C) (hprojected : P v ∈ C) : v ∈ C := by
  have h := C.add_mem hquotient hprojected
  simpa only [sub_add_cancel] using h

end Raising

section Jacobi

variable {K Q Z : Type*} [Field K]
variable [AddCommGroup Q] [Module K Q] [AddCommGroup Z] [Module K Z]

/-- The scalar cancellation used at a bottom-triplet Jacobi witness.
Here `f = F(a,-)`, `g = F(b,-)`, `u = beta(a,p)`, and `v = beta(b,p)`.
The Jacobi identity and normal-product controls supply `hjacobi`; current
weights supply `hu`; the exact certificate supplies `hv` and `hc`. -/
theorem jacobi_bottom_witness
    (f g : Q →ₗ[K] Z) (u v q : Q) (c : K)
    (hjacobi : f v = g u) (hu : u = 0)
    (hv : v = c • q) (hc : c ≠ 0) : f q = 0 := by
  have hscaled : c • f q = 0 := by
    simpa [hv, hu] using hjacobi
  have h := congrArg (fun z : Z => c⁻¹ • z) hscaled
  simpa [smul_smul, hc] using h

end Jacobi

#print axioms nilpotent_raising_saturation
#print axioms projected_residual_recovery
#print axioms jacobi_bottom_witness

end HaagerupIzumi.CFT
