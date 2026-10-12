module

public import HaagerupIzumi.C8.Lattice.ModeQ

@[expose] public section

/-!
# `modeQ` with a rational operator: fewer coefficient multiplications

Profiling of `modeQ` (`drafts/ModeQProbeSplit.lean`, `Lattice/Benchmark.md` §5): for `E_R(0)` on
20 states of the triplet about three quarters of the kernel time is coefficient arithmetic
(`QA.mul` = sixteen rational products and their normalizations).  The currents and `ω` are
*rational* vectors, so `modeQR a m b` (rational `a`, `QVec` `b`) scales the four rational
components of each coefficient of `b` by a rational number (`smulR`: four products instead of
`QA.mul c (QA.ofRat r)`, sixteen).

**Link**: `toVQ_modeQR`: `toVQ (modeQR a m b) = modeC m (toV a) (toVQ b)` for canonical
states.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- `r · c` for `r ∈ ℚ`, `c ∈ ℚ(√13, √-3)`. -/
def smulR (r : ℚ) (c : QA) : QA := ⟨r * c.a, r * c.b, r * c.c, r * c.d⟩

theorem toC_smulR (r : ℚ) (c : QA) : (smulR r c).toC = (r : ℂ) * c.toC := by
  simp only [smulR, QA.toC]
  push_cast
  ring

/-- `c · v` for a rational vector `v` (as `liftQ`, with `smulR`). -/
def liftR (c : QA) (v : Vec) : QVec := v.map fun p => (p.1, smulR p.2 c)

theorem toVQ_liftR (c : QA) : ∀ v : Vec, toVQ (liftR c v) = c.toC • toV v
  | [] => by simp [liftR, toVQ_nil]
  | (s, r) :: v => by
    have ih := toVQ_liftR c v
    have e1 : toV [(s, 1)] = Finsupp.single (canon s) 1 := by
      rw [toV_cons_mk, toV_nil, add_zero, Rat.cast_one]
    show toVQ ((s, smulR r c) :: liftR c v) = c.toC • toV ((s, r) :: v)
    rw [toVQ_cons, ih]
    show (smulR r c).toC • toV [(s, 1)] + c.toC • toV v = c.toC • toV ((s, r) :: v)
    rw [toC_smulR, toV_cons_mk s r v, e1, smul_add, Finsupp.smul_single, Finsupp.smul_single,
      smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

/-- `a_(m) b` for a rational vector `a`. -/
def modeQR (a : Vec) (m : ℤ) (b : QVec) : QVec :=
  a.flatMap fun p => b.flatMap fun q => liftR (smulR p.2 q.2) (basisMode p.1 m q.1)

theorem toVQ_modeQR_single {s : State} (hs : Valid s) (c : ℚ) (m : ℤ) :
    ∀ b : QVec, (∀ q ∈ b, Valid q.1) →
      toVQ (b.flatMap fun q => liftR (smulR c q.2) (basisMode s m q.1)) =
        (c : ℂ) • modeC m (toV [(s, 1)]) (toVQ b)
  | [], _ => by simp [toVQ_nil]
  | q :: b, hb => by
    have ih := toVQ_modeQR_single hs c m b fun r hr => hb r (List.mem_cons_of_mem _ hr)
    rw [List.flatMap_cons, toVQ_append, ih, toVQ_liftR, toVQ_cons, map_add, map_smul,
      modeC_single_states hs (hb q List.mem_cons_self), toC_smulR, smul_add, smul_smul]

/-- **Link**: `modeQR` computes `modeC` on vectors of canonical states. -/
theorem toVQ_modeQR (m : ℤ) : ∀ (a : Vec) (b : QVec), (∀ p ∈ a, Valid p.1) →
    (∀ q ∈ b, Valid q.1) → toVQ (modeQR a m b) = modeC m (toV a) (toVQ b)
  | [], b, _, _ => by simp [modeQR, toVQ_nil]
  | (s, c) :: a, b, ha, hb => by
    have hs : Valid s := ha (s, c) List.mem_cons_self
    have ih := toVQ_modeQR m a b (fun r hr => ha r (List.mem_cons_of_mem _ hr)) hb
    have h1 := toVQ_modeQR_single hs c m b hb
    simp only [modeQR] at ih ⊢
    rw [List.flatMap_cons, toVQ_append, h1, ih,
      show toV ((s, c) :: a) = (c : ℂ) • toV [(s, 1)] + toV a by
        rw [← toV_single_state, toV_cons_mk, toV_cons_mk, toV_nil, add_zero],
      map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

#print axioms toVQ_modeQR

end LatticeVOA
end HaagerupIzumi.C8
