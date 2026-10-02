module

public import HaagerupIzumi.C8.Lattice.Roots

@[expose] public section

/-!
# Kernel micro-benchmarks for the W2 estimate

Work item W1 (benchmark), `C8/ROADMAP.md`.  The certificates of `ProofMap` live over
`ℚ(√13, √-3)` with coefficients of up to 290 bits
(`hi_cft_20260923_next_structure_lower_closure.json`), whereas the cross-check samples of
`Lattice/Samples*.lean` only have small rational coefficients.  This file measures the kernel
cost of the field arithmetic itself (`set_option profiler true` prints the time of each check):

* `QA`: `ℚ(√13, √-3)` in the basis `1, s, t, st` (`s² = 13`, `t² = -3`) of
  `hi_cft_20260923_c8_exact.py` (class `A`), with the multiplication table of `A.__mul__`.
* `qa_pow_bench`: `x^48` computed in two ways (`48` sequential multiplications against
  `x^24 · x^24`) for `x = 1/2 + s/3 + t/5 + st/7`; the coefficients reach several hundred bits.
* `rat_sum_bench`: a sum of `400` rationals with distinct denominators (normalization cost).
* Duplicate checks on the 78 integer keys of `roots` (3003 comparisons), to separate the cost
  of the `Decidable` instances from the comparisons themselves: `roots_keys_nodup`
  (`List.Nodup`, `decide +kernel`, in `Lattice/Roots.lean`) against the Boolean checkers
  `allDistinctZ` (`Int` equality) and `allDistinctN` (`Nat.beq` on natural keys).

These are benchmarks, not mathematical statements used elsewhere.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 5
set_option Elab.async false

/-- `ℚ(√13, √-3)` in the basis `1, s, t, st`. -/
structure QA where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

/-- Multiplication: `s² = 13`, `t² = -3`, `(st)² = -39`, `s·st = 13t`, `t·st = -3s`. -/
def QA.mul (x y : QA) : QA :=
  ⟨x.a * y.a + 13 * (x.b * y.b) - 3 * (x.c * y.c) - 39 * (x.d * y.d),
   x.a * y.b + x.b * y.a - 3 * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a + 13 * (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩

/-- `x^n` by `n` sequential multiplications. -/
def QA.pow (x : QA) : ℕ → QA
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => QA.mul (QA.pow x n) x

/-- The test element `1/2 + s/3 + t/5 + st/7`. -/
def qaX : QA := ⟨1 / 2, 1 / 3, 1 / 5, 1 / 7⟩

theorem qa_pow_bench : QA.pow qaX 48 = QA.mul (QA.pow qaX 24) (QA.pow qaX 24) := by
  decide +kernel

/-- `∑_{k < n} 1/(k+1)` (harmonic numbers: denominators grow, every addition normalizes). -/
def harm : ℕ → ℚ
  | 0 => 0
  | n + 1 => harm n + 1 / ((n : ℚ) + 1)

theorem rat_sum_bench : harm 400 - harm 399 = 1 / 400 := by
  decide +kernel

/-- Boolean duplicate check with `Int` equality. -/
def allDistinctZ : List ℤ → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !decide (x = y)) && allDistinctZ xs

/-- Boolean duplicate check with the kernel-accelerated `Nat.beq`. -/
def allDistinctN : List ℕ → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !Nat.beq x y) && allDistinctN xs

theorem roots_keys_distinctZ : allDistinctZ (roots.map Mom.key) = true := by
  decide +kernel

theorem roots_keys_distinctN :
    allDistinctN (roots.map fun r => (Mom.key r + 100000000).toNat) = true := by
  decide +kernel

#print axioms qa_pow_bench
#print axioms rat_sum_bench
#print axioms roots_keys_distinctN

end LatticeVOA
end HaagerupIzumi.C8
