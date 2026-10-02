module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Multi-dimensional Poisson summation

Foundational analytic input for work item W6 (`C8/ROADMAP.md`, the theta identities after
pole cancellation in the proof of Proposition `prop:near-group-current-obstructions`, lines
3614–3770 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).  Mathlib has Poisson summation
only on `ℝ` (`Real.tsum_eq_tsum_fourier`); this file proves it on `ℝ^d = d → ℝ` for any finite
index type `d`.

## Main result

`tsum_eq_tsum_fourierPi`: let `f : C(ℝ^d, ℂ)` be such that for every compact `K` the sup norms
of the translates `f(· + m)|_K`, `m ∈ ℤ^d`, are summable (`TranslatesSummable f`), and let the
values `𝓕f(k)`, `k ∈ ℤ^d`, of the Fourier transform `𝓕f(ξ) = ∫ e(-x·ξ) f(x) dx` be summable,
where `e(r) = exp(2πir)` (`eChar`).  Then for every `x ∈ ℝ^d`
`∑_{m ∈ ℤ^d} f(x + m) = ∑_{k ∈ ℤ^d} 𝓕f(k) e(k·x)`.

## Method (chosen after a feasibility check)

We periodize and use Fourier series on the torus `UnitAddTorus d`, which Mathlib has
(`Analysis/Fourier/AddCircleMulti.lean`), instead of iterating the one-dimensional theorem
coordinatewise: the latter needs partial Fourier transforms and a class of functions closed
under them, which Mathlib does not provide, while the torus route needs only
* the descent of the periodization `∑_m f(· + m)` to `(ℝ/ℤ)^d` (a product of open quotient
  maps is a quotient map, `IsOpenQuotientMap.piMap`);
* the computation of its Fourier coefficients: the half-open cube `(0,1]^d` is a fundamental
  domain for `ℤ^d` (`isAddFundamentalDomain_unitBox`), so integrals over `ℝ^d` unfold into
  sums of integrals over the cube (`integral_eq_tsum_unitBox`);
* Mathlib's theorem that an absolutely summable multivariate Fourier series of a continuous
  function converges pointwise to it (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex MeasureTheory Set TopologicalSpace Filter Topology

namespace HaagerupIzumi.C8
namespace Theta

/-! ## The additive character `e(r) = exp(2πir)` -/

/-- `e(r) = exp(2πir)`. -/
def eChar (r : ℝ) : ℂ := cexp (↑(2 * π * r) * I)

theorem eChar_add (r s : ℝ) : eChar (r + s) = eChar r * eChar s := by
  simp only [eChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eChar_intCast (n : ℤ) : eChar n = 1 := by
  rw [eChar, ← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1
  push_cast
  ring

theorem eChar_zero : eChar 0 = 1 := by
  simpa using eChar_intCast 0

theorem eChar_neg (r : ℝ) : eChar (-r) = (eChar r)⁻¹ := by
  rw [eChar, eChar, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_eChar (r : ℝ) : ‖eChar r‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_eChar : Continuous eChar :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

variable {d : Type*}

/-! ## Integer vectors and the torus `(ℝ/ℤ)^d` as a quotient of `ℝ^d` -/

/-- An integer vector `m ∈ ℤ^d` as a real vector. -/
def intVec (m : d → ℤ) : d → ℝ := fun i => (m i : ℝ)

@[simp] theorem intVec_apply (m : d → ℤ) (i : d) : intVec m i = (m i : ℝ) := rfl

theorem intVec_add (m n : d → ℤ) : intVec (m + n) = intVec m + intVec n := by
  ext i
  simp [intVec]

theorem intVec_neg (m : d → ℤ) : intVec (-m) = -intVec m := by
  ext i
  simp [intVec]

theorem intVec_zero : intVec (0 : d → ℤ) = 0 := by
  ext i
  simp [intVec]

theorem intVec_injective : Function.Injective (intVec (d := d)) := by
  intro m n h
  funext i
  have hi := congrFun h i
  simp only [intVec_apply] at hi
  exact_mod_cast hi

/-- The projection `ℝ^d → (ℝ/ℤ)^d`. -/
def torusProj : C(d → ℝ, UnitAddTorus d) where
  toFun x i := (x i : UnitAddCircle)
  continuous_toFun := continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)

theorem isQuotientMap_torusProj : IsQuotientMap (torusProj (d := d)) :=
  (IsOpenQuotientMap.piMap (f := fun (_ : d) (x : ℝ) => (x : UnitAddCircle))
    fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

theorem exists_eq_add_intVec_of_torusProj_eq {x y : d → ℝ} (h : torusProj x = torusProj y) :
    ∃ n : d → ℤ, x = y + intVec n := by
  have key : ∀ i, ∃ n : ℤ, x i = y i + n := by
    intro i
    have hi : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun h i
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hi.symm)
    refine ⟨n, ?_⟩
    rw [Int.smul_one_eq_cast] at hn
    linarith
  choose n hn using key
  exact ⟨n, funext fun i => by simp [hn i]⟩

variable [Fintype d]

/-! ## The Fourier transform on `ℝ^d` -/

theorem intVec_dotProduct (m n : d → ℤ) : intVec m ⬝ᵥ intVec n = ((m ⬝ᵥ n : ℤ) : ℝ) := by
  simp only [intVec, dotProduct, Int.cast_sum, Int.cast_mul]

/-- The Fourier transform on `ℝ^d` with the kernel `e(-x·ξ)`:
`𝓕f(ξ) = ∫ e(-x·ξ) f(x) dx`. -/
def fourierPi (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ := ∫ x, eChar (-(x ⬝ᵥ ξ)) * f x

/-- `e(-(x + m)·k) = e(-x·k)` for integer vectors `m, k`. -/
theorem eChar_neg_dot_add_intVec (x : d → ℝ) (m k : d → ℤ) :
    eChar (-((x + intVec m) ⬝ᵥ intVec k)) = eChar (-(x ⬝ᵥ intVec k)) := by
  rw [add_dotProduct, intVec_dotProduct, neg_add, ← Int.cast_neg, eChar_add, eChar_intCast,
    mul_one]

theorem continuous_eChar_neg_dot (ξ : d → ℝ) :
    Continuous fun x : d → ℝ => eChar (-(x ⬝ᵥ ξ)) :=
  continuous_eChar.comp (continuous_id.dotProduct continuous_const).neg

/-! ## The periodization and its descent to the torus -/

/-- Hypothesis of Poisson summation: on every compact set the sup norms of the translates
`f(· + m)`, `m ∈ ℤ^d`, are summable. -/
def TranslatesSummable (f : C(d → ℝ, ℂ)) : Prop :=
  ∀ K : Compacts (d → ℝ), Summable fun m : d → ℤ =>
    ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict K‖

/-- The periodization `∑_{m ∈ ℤ^d} f(· + m)` (a locally uniformly convergent sum). -/
def periodize (f : C(d → ℝ, ℂ)) : C(d → ℝ, ℂ) :=
  ∑' m : d → ℤ, f.comp (ContinuousMap.addRight (intVec m))

variable {f : C(d → ℝ, ℂ)}

theorem periodize_apply (hf : TranslatesSummable f) (x : d → ℝ) :
    periodize f x = ∑' m : d → ℤ, f (x + intVec m) := by
  rw [periodize, ← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hf)]
  rfl

theorem periodize_add_intVec (hf : TranslatesSummable f) (x : d → ℝ) (n : d → ℤ) :
    periodize f (x + intVec n) = periodize f x := by
  rw [periodize_apply hf, periodize_apply hf]
  conv_rhs => rw [← (Equiv.addLeft n).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addLeft, intVec_add, add_assoc]

theorem periodize_factorsThrough (hf : TranslatesSummable f) :
    Function.FactorsThrough (periodize f) (torusProj (d := d)) := by
  intro x y h
  obtain ⟨n, rfl⟩ := exists_eq_add_intVec_of_torusProj_eq h
  exact periodize_add_intVec hf y n

/-- The periodization as a continuous function on the torus `(ℝ/ℤ)^d`. -/
def periodizeTorus (f : C(d → ℝ, ℂ)) (hf : TranslatesSummable f) : C(UnitAddTorus d, ℂ) :=
  isQuotientMap_torusProj.lift (periodize f) (periodize_factorsThrough hf)

theorem periodizeTorus_apply (hf : TranslatesSummable f) (x : d → ℝ) :
    periodizeTorus f hf (fun i => (x i : UnitAddCircle)) = periodize f x :=
  DFunLike.congr_fun
    (isQuotientMap_torusProj.lift_comp (periodize f) (periodize_factorsThrough hf)) x

/-- The monomial `mFourier k` evaluated at the image of `x ∈ ℝ^d` is `e(k·x)`. -/
theorem mFourier_coe (k : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) = eChar (intVec k ⬝ᵥ x) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply, eChar]
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, intVec]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## The cube `(0,1]^d` is a fundamental domain for `ℤ^d` -/

/-- `ℤ^d → ℝ^d` as an additive group homomorphism. -/
def intVecHom : (d → ℤ) →+ (d → ℝ) where
  toFun := intVec
  map_zero' := intVec_zero
  map_add' := intVec_add

/-- The lattice `ℤ^d ⊂ ℝ^d` is parametrized by `ℤ^d`. -/
def intLatticeEquiv : (d → ℤ) ≃ (intVecHom (d := d)).range :=
  (AddMonoidHom.ofInjective (f := intVecHom) intVec_injective).toEquiv

omit [Fintype d] in
theorem intLatticeEquiv_apply (m : d → ℤ) :
    ((intLatticeEquiv m : (intVecHom (d := d)).range) : d → ℝ) = intVec m :=
  AddMonoidHom.ofInjective_apply _

instance countable_intLattice : Countable (intVecHom (d := d)).range :=
  (intLatticeEquiv (d := d)).symm.injective.countable

/-- The half-open unit cube `(0,1]^d`. -/
def unitBox (d : Type*) : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

theorem measurableSet_unitBox : MeasurableSet (unitBox d) :=
  MeasurableSet.univ_pi' fun _ => measurableSet_Ioc

/-- The closed unit cube `[0,1]^d` (a compact set containing `unitBox d`). -/
def unitCube (d : Type*) [Fintype d] : Compacts (d → ℝ) :=
  ⟨Set.pi Set.univ fun _ => Icc (0 : ℝ) 1, isCompact_univ_pi fun _ => isCompact_Icc⟩

theorem unitBox_subset_unitCube : unitBox d ⊆ (unitCube d : Set (d → ℝ)) := by
  intro x hx
  show x ∈ Set.pi Set.univ fun _ => Icc (0 : ℝ) 1
  exact fun i _ => Ioc_subset_Icc_self (hx i)

theorem volume_unitBox_lt_top : volume (unitBox d) < ⊤ :=
  (measure_mono unitBox_subset_unitCube).trans_lt (unitCube d).isCompact.measure_lt_top

theorem isAddFundamentalDomain_unitBox :
    IsAddFundamentalDomain (intVecHom (d := d)).range (unitBox d) volume := by
  refine IsAddFundamentalDomain.mk' measurableSet_unitBox.nullMeasurableSet fun x => ?_
  have hp : (0 : ℝ) < 1 := one_pos
  let n : d → ℤ := fun i => toIocDiv hp 0 (x i)
  refine ⟨intLatticeEquiv (-n), ?_, ?_⟩
  · intro i
    have h := sub_toIocDiv_zsmul_mem_Ioc hp 0 (x i)
    rw [zero_add, Int.smul_one_eq_cast] at h
    show ((intLatticeEquiv (-n) : d → ℝ) + x) i ∈ Ioc (0 : ℝ) 1
    rw [intLatticeEquiv_apply, Pi.add_apply, intVec_apply, Pi.neg_apply, Int.cast_neg,
      neg_add_eq_sub]
    exact h
  · intro g hg
    obtain ⟨m, rfl⟩ := intLatticeEquiv.surjective g
    rw [intLatticeEquiv.apply_eq_iff_eq]
    funext i
    have hi : ((intLatticeEquiv m : d → ℝ) + x) i ∈ Ioc (0 : ℝ) 1 := hg i
    rw [intLatticeEquiv_apply, Pi.add_apply, intVec_apply] at hi
    have h2 : x i - (-m i) • (1 : ℝ) = (m i : ℝ) + x i := by
      rw [Int.smul_one_eq_cast, Int.cast_neg]
      ring
    have h3 : x i - (-m i) • (1 : ℝ) ∈ Ioc 0 (0 + 1) := by
      rw [h2, zero_add]
      exact hi
    have h4 := (toIocDiv_eq_iff hp).2 h3
    simp [n, h4]

/-- Unfolding an integral over `ℝ^d` into integrals over the translates of the cube. -/
theorem integral_eq_tsum_unitBox {g : (d → ℝ) → ℂ} (hg : Integrable g) :
    ∫ x, g x = ∑' m : d → ℤ, ∫ x in unitBox d, g (x + intVec m) := by
  rw [isAddFundamentalDomain_unitBox.integral_eq_tsum'' g hg, ← intLatticeEquiv.tsum_eq]
  refine tsum_congr fun m => ?_
  refine setIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
  show g ((intLatticeEquiv m : d → ℝ) + x) = g (x + intVec m)
  rw [intLatticeEquiv_apply, add_comm]

theorem lintegral_eq_tsum_unitBox (g : (d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' m : d → ℤ, ∫⁻ x in unitBox d, g (x + intVec m) := by
  rw [isAddFundamentalDomain_unitBox.lintegral_eq_tsum'' g, ← intLatticeEquiv.tsum_eq]
  refine tsum_congr fun m => ?_
  refine setLIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
  show g ((intLatticeEquiv m : d → ℝ) + x) = g (x + intVec m)
  rw [intLatticeEquiv_apply, add_comm]

/-! ## Integrability and the Fourier coefficients of the periodization -/

theorem norm_le_restrict_unitCube (f : C(d → ℝ, ℂ)) (m : d → ℤ) {x : d → ℝ}
    (hx : x ∈ unitBox d) :
    ‖f (x + intVec m)‖ ≤ ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict (unitCube d)‖ := by
  have h := ((f.comp (ContinuousMap.addRight (intVec m))).restrict
    (unitCube d : Set (d → ℝ))).norm_coe_le_norm ⟨x, unitBox_subset_unitCube hx⟩
  exact h

/-- A function with summable translates is integrable on `ℝ^d`. -/
theorem integrable_of_translatesSummable (hf : TranslatesSummable f) :
    Integrable (f : (d → ℝ) → ℂ) := by
  refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
  have hC := hf (unitCube d)
  show ∫⁻ x, ‖f x‖ₑ < ⊤
  rw [lintegral_eq_tsum_unitBox]
  calc ∑' m : d → ℤ, ∫⁻ x in unitBox d, ‖f (x + intVec m)‖ₑ
      ≤ ∑' m : d → ℤ, ENNReal.ofReal
          ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict (unitCube d)‖ *
          volume (unitBox d) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        refine (setLIntegral_mono measurable_const fun x hx => ?_).trans_eq
          (setLIntegral_const _ _)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_le_restrict_unitCube f m hx)
    _ = ENNReal.ofReal (∑' m : d → ℤ,
          ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict (unitCube d)‖) *
          volume (unitBox d) := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) hC]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top volume_unitBox_lt_top

/-- The `k`-th Fourier coefficient of the periodization is `𝓕f(k)`. -/
theorem mFourierCoeff_periodizeTorus (hf : TranslatesSummable f) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodizeTorus f hf) k = fourierPi f (intVec k) := by
  have hC := hf (unitCube d)
  have hcont : ∀ m : d → ℤ,
      Continuous fun x : d → ℝ => eChar (-(x ⬝ᵥ intVec k)) * f (x + intVec m) := fun m =>
    (continuous_eChar_neg_dot _).mul (f.continuous.comp (continuous_id.add continuous_const))
  have hint : ∀ m : d → ℤ, Integrable
      (fun x : d → ℝ => eChar (-(x ⬝ᵥ intVec k)) * f (x + intVec m))
      (volume.restrict (unitBox d)) := fun m =>
    ((hcont m).continuousOn.integrableOn_compact (unitCube d).isCompact).mono_set
      unitBox_subset_unitCube
  have hsum : Summable fun m : d → ℤ =>
      ∫ x in unitBox d, ‖eChar (-(x ⬝ᵥ intVec k)) * f (x + intVec m)‖ := by
    refine (hC.mul_right (volume.real (unitBox d))).of_norm_bounded fun m => ?_
    refine norm_setIntegral_le_of_norm_le_const_ae' volume_unitBox_lt_top
      (Eventually.of_forall fun x hx => ?_)
    rw [norm_norm, norm_mul, norm_eChar, one_mul]
    exact norm_le_restrict_unitCube f m hx
  have hint' : Integrable fun x : d → ℝ => eChar (-(x ⬝ᵥ intVec k)) * f x := by
    refine (integrable_of_translatesSummable hf).norm.mono'
      ((continuous_eChar_neg_dot _).mul f.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_eChar, one_mul]
  have hbox : {x : d → ℝ | ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} = unitBox d := by
    ext x
    simp [unitBox]
  have h1 : ∀ x : d → ℝ, UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
      periodizeTorus f hf (fun i => (x i : UnitAddCircle)) =
        ∑' m : d → ℤ, eChar (-(x ⬝ᵥ intVec k)) * f (x + intVec m) := by
    intro x
    rw [smul_eq_mul, mFourier_coe, periodizeTorus_apply hf, periodize_apply hf, tsum_mul_left,
      intVec_neg, neg_dotProduct, dotProduct_comm (intVec k) x]
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k 0, hbox]
  refine Eq.trans (setIntegral_congr_fun measurableSet_unitBox fun x _ => h1 x) ?_
  refine Eq.trans (integral_tsum_of_summable_integral_norm (μ := volume.restrict (unitBox d))
    (F := fun m x => eChar (-(x ⬝ᵥ intVec k)) * f (x + intVec m)) hint hsum).symm ?_
  rw [fourierPi, integral_eq_tsum_unitBox hint']
  refine tsum_congr fun m => setIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
  simp only [eChar_neg_dot_add_intVec]

/-! ## Poisson summation -/

/-- **Poisson summation on `ℝ^d`.**  If the translates of `f` have locally summable sup
norms and `k ↦ 𝓕f(k)` is summable on `ℤ^d`, then for every `x`
`∑_{m ∈ ℤ^d} f(x + m) = ∑_{k ∈ ℤ^d} 𝓕f(k) e(k·x)`. -/
theorem tsum_eq_tsum_fourierPi (hf : TranslatesSummable f)
    (hF : Summable fun k : d → ℤ => fourierPi f (intVec k)) (x : d → ℝ) :
    ∑' m : d → ℤ, f (x + intVec m) =
      ∑' k : d → ℤ, fourierPi f (intVec k) * eChar (intVec k ⬝ᵥ x) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (periodizeTorus f hf)) := by
    have : UnitAddTorus.mFourierCoeff (periodizeTorus f hf) =
        fun k => fourierPi f (intVec k) := funext (mFourierCoeff_periodizeTorus hf)
    rw [this]
    exact hF
  have h := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs
    (fun i => (x i : UnitAddCircle))).tsum_eq
  rw [periodizeTorus_apply hf, periodize_apply hf] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [smul_eq_mul, mFourier_coe, mFourierCoeff_periodizeTorus hf]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.isAddFundamentalDomain_unitBox
#print axioms HaagerupIzumi.C8.Theta.mFourierCoeff_periodizeTorus
#print axioms HaagerupIzumi.C8.Theta.tsum_eq_tsum_fourierPi
