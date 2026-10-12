module

public import HaagerupIzumi.C8.ProofMapConcreteVacuum
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

@[expose] public section

/-!
# The rigidity arrow of the proof map, made concrete

Lemma `lem:projective-unit` (lines 2980–3012 of `c8_expanded_20260929/haagerup_c8_expanded.tex`),
applied in Theorem `thm:positive-stress-rationality` (lines 3014–3032), is the arrow

* `L_rigid : projectiveVacuum → c2Cofinite → initialGrades → rigidSemisimple`.

The concrete object is a monoidal category `𝒞` (the category `Rep(U)` of grading-restricted
generalized `U`-modules, McRae Sections 2.3, 3).  `rigidNodes R 𝒞` overrides `rigidSemisimple` by
`RigidSemisimple 𝒞`: every object has a right dual (rigidity; only right duals are recorded, and
`𝒞` is modelled as a monoidal category without its braiding) and every object is projective
(semisimplicity of the abelian category `𝒞`).

`rigid_arrow` proves the last step of `lem:projective-unit` (lines 3007–3012): once every object
`Y` has a right dual, `Hom(Y, -) ≅ Hom(𝟙, - ⊗ Y*)` and `- ⊗ Y*` preserves epimorphisms (it is a
left adjoint, `Y*` having a right dual), so the projectivity of `𝟙` gives the projectivity of
every `Y` (`projective_of_rigid`, via `tensorRightAdjunction` and `Adjunction.map_projective`).
Remaining inputs: `hunit` ([definitional]: `𝟙 = U`, and `VacuumIsProjective` is projectivity of
`𝟙` in `𝒞`) and `hEP` ([external] rigidity, see its docstring).
-/

namespace HaagerupIzumi.C8.ProofMap

open CategoryTheory MonoidalCategory

universe v u

/-- `𝒞` is rigid and semisimple: every object has a right dual and every object is projective. -/
def RigidSemisimple (𝒞 : Type u) [Category.{v} 𝒞] [MonoidalCategory 𝒞] : Prop :=
  (∀ X : 𝒞, Nonempty (HasRightDual X)) ∧ ∀ X : 𝒞, Projective X

/-- The proof map with `rigidSemisimple` made concrete. -/
def rigidNodes (R : Nodes) (𝒞 : Type u) [Category.{v} 𝒞] [MonoidalCategory 𝒞] : Nodes :=
  { R with rigidSemisimple := RigidSemisimple 𝒞 }

/-- **Every object is projective** (lines 3007–3012): in a monoidal category in which every object
has a right dual, projectivity of the unit gives projectivity of every object. -/
theorem projective_of_rigid {𝒞 : Type u} [Category.{v} 𝒞] [MonoidalCategory 𝒞]
    (hdual : ∀ X : 𝒞, Nonempty (HasRightDual X)) (h1 : Projective (𝟙_ 𝒞)) (Y : 𝒞) :
    Projective Y := by
  obtain ⟨hY⟩ := hdual Y
  obtain ⟨hY'⟩ := hdual Yᘁ
  have : (tensorRight Yᘁ).IsLeftAdjoint := (tensorRightAdjunction Yᘁ Yᘁᘁ).isLeftAdjoint
  exact Projective.of_iso (λ_ Y) ((tensorRightAdjunction Y Yᘁ).map_projective (𝟙_ 𝒞) h1)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **`L_rigid`** (Lemma `lem:projective-unit` with McRae and Etingof–Penneys, lines 2980–3012).

* Concrete nodes: `projectiveVacuum` (`VacuumNode`, through `hunit`), `c2Cofinite` (finite
  category, applied to `hEP`), `rigidSemisimple` (`RigidSemisimple 𝒞`).  The opaque part `init` of
  `initialGrades` (unitarity, hence `U' = U`) is applied to `hEP`.
* Concrete theorem: `projective_of_rigid`.
* Remaining inputs: `hunit` ([definitional] `𝒞` is the category of grading-restricted generalized
  `U`-modules with unit `U`, so `VacuumIsProjective` is the projectivity of `𝟙`), and `hEP`:
  [external] McRae Sections 2.3, 3 (`𝒞` is a finite braided Grothendieck–Verdier category with
  right-exact tensor product and dualizing object `U' = U`, from `C₂`-cofiniteness and unitarity)
  and Etingof–Penneys Theorem 1.1 (non-negligible objects of moderate growth are rigid), with the
  [manuscript step] of lines 2992–3006: moderate growth from right exactness (the growth estimate is
  formalized: `eventually_sq_mul_pow_lt_factorial`, Regularity/Energy) and non-negligibility from
  the splitting of the Grothendieck–Verdier evaluation `DX ⊗ X → 𝟙` by projectivity of `𝟙`. -/
theorem rigid_arrow {Simp : Type*} (S : StressData E H) (SD : SimpleData Simp) (𝒞 : Type u)
    [Category.{v} 𝒞] [MonoidalCategory 𝒞] (init : Prop)
    (hunit : VacuumNode S SD → Projective (𝟙_ 𝒞))
    (hEP : FiniteDimensional ℂ (H ⧸ C2 S.U) → init → Projective (𝟙_ 𝒞) →
      ∀ X : 𝒞, Nonempty (HasRightDual X)) :
    VacuumNode S SD → FiniteDimensional ℂ (H ⧸ C2 S.U) → init → RigidSemisimple 𝒞 := by
  intro hv hc2 hinit
  have h1 := hunit hv
  have hdual := hEP hc2 hinit h1
  exact ⟨hdual, projective_of_rigid hdual h1⟩

#print axioms projective_of_rigid
#print axioms rigid_arrow

end HaagerupIzumi.C8.ProofMap
