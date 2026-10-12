module

public import HaagerupIzumi.C8.Lattice.S2Core

@[expose] public section

/-!
# Membership in the current space `K` by kernel evaluation

For the lower certificate `K_(1) S₂ ⊆ K` (`LowerCertificate.KS₂1`, Certificate `cert:lower`,
lines 2253–2266 of `c8_expanded_20260929/haagerup_c8_expanded.tex`): a vector `v` of weight
one over `ℚ(√13, √-3)` lies in `K = span(H_L, E_L, F_L, H_R, E_R, F_R)` if it equals the
combination `kDec v` of the six currents whose coefficients are read off at one pivot state of
each current (a state occurring in that current only: `h₅(-1)𝟏` for `H_L`, `h₆(-1)𝟏` for `H_R`,
`e^{∓α_L}` for `E_L`, `F_L`, `e^{±α₀}` for `E_R`, `F_R`).  `kOK v` is that equality, decided by
kernel evaluation; `toV4_mem_Kspan_of_kOK` is its meaning.  No coefficient data are needed: the
kernel computes both the mode and the decomposition.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- Pivot states of `H_L` (coefficient `-2`), `E_L` (`1`), `F_L` (`-1`), `H_R` (`2`), `E_R` (`1`),
`F_R` (`-5`). -/
def pivHL : State := S 0 0 0 0 0 0 0 0 [5]
def pivEL : State := S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []
def pivFL : State := S 1 2 3 2 1 2 0 0 []
def pivHR : State := S 0 0 0 0 0 0 0 0 [6]
def pivER : State := S 1 0 0 0 0 0 0 0 []
def pivFR : State := S (-1) 0 0 0 0 0 0 0 []

/-- The decomposition of a weight-one vector along the six currents, with the coefficients read
off at the pivot states. -/
def kDec (v : Vec4) : List (QA × Vec4) :=
  [(QA.mul (Vec4.coeff v pivHL) (QA.ofRat (-1 / 2)), Vec4.ofVec hL),
   (Vec4.coeff v pivEL, Vec4.ofVec eL),
   (QA.mul (Vec4.coeff v pivFL) (QA.ofRat (-1)), Vec4.ofVec fL),
   (QA.mul (Vec4.coeff v pivHR) (QA.ofRat (1 / 2)), Vec4.ofVec hR),
   (Vec4.coeff v pivER, Vec4.ofVec eR),
   (QA.mul (Vec4.coeff v pivFR) (QA.ofRat (-1 / 5)), Vec4.ofVec fR)]

/-- `v` equals its decomposition along the currents. -/
def kOK (v : Vec4) : Bool := decide (v = combo (kDec v))

/-- **Meaning of `kOK`**: a vector that equals its decomposition lies in `K`. -/
theorem toV4_mem_Kspan_of_kOK {v : Vec4} (h : kOK v = true) : toV4 v ∈ Kspan := by
  have hv : v = combo (kDec v) := of_decide_eq_true h
  rw [hv]
  refine toV4_combo_mem _ fun p hp => ?_
  simp only [kDec, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [toV4_ofVec] <;>
    exact current_mem_Kspan (by simp)

/-- Sanity check of the pivots: each current is its own decomposition. -/
theorem kOK_currents : kOK (Vec4.ofVec hL) = true ∧ kOK (Vec4.ofVec eL) = true ∧
    kOK (Vec4.ofVec fL) = true ∧ kOK (Vec4.ofVec hR) = true ∧ kOK (Vec4.ofVec eR) = true ∧
    kOK (Vec4.ofVec fR) = true := by
  decide +kernel

#print axioms toV4_mem_Kspan_of_kOK
#print axioms kOK_currents

end LatticeVOA
end HaagerupIzumi.C8
