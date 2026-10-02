module

public import HaagerupIzumi.C8.Lattice.Fock

@[expose] public section

/-!
# Modes of the lattice vertex algebra `V_L` on Fock monomials (computable)

Work item W1 of `C8/ROADMAP.md`; Appendix A of
`c8_expanded_20260929/haagerup_c8_expanded.tex` (lattice construction, lines 1872–1910).  The
functions below are a line-by-line transcription of the engine used by the certificates,
`hi_cft_20260923_proof_general_modes_v2.py` (`vertex`, `basis_mode`) installed into
`hi_cft_20260923_c8_exact.py` (`heis`, `cocycle`) with the Schur coefficients of
`hi_cft_20260923_proof_exact4.py` (`creation`), **without the grade ceiling**: the Python code
returns `()` above `MAX_GRADE = 4`; here every mode is computed exactly (the grade of the output
bounds every intermediate degree, so nothing is truncated).

## Conventions (FLM)

* `Y(u, z) = ∑ₙ u_(n) z^{-n-1}`; `basisMode u n v = u_(n) v` on Fock monomials
  (`Lattice/Fock.lean`), `mode` its bilinear extension to sparse vectors.
* Heisenberg: `hᵢ(m) = (hᵢ)_(m)` for `hᵢ = αᵢ(-1)𝟏`, `[hᵢ(m), hⱼ(n)] = m (αᵢ,αⱼ) δ_{m+n,0}`,
  `hᵢ(0) = (αᵢ, β)` on momentum `β`, `hᵢ(m) e^β = 0` for `m > 0` (`heis`).  Oscillators are
  unnormalized: the state with code list `[k, k]` is `hᵢ(-n)² e^β`, not divided by `2!`.
* Vertex operator of `e^α` (`vertexOp`):
  `Y(e^α, z) = E⁻(-α, z) E⁺(-α, z) e_α z^α`, with
  `E⁻(-α,z) = exp(∑_{n>0} α(-n) zⁿ/n)`, `E⁺(-α,z) = exp(-∑_{n>0} α(n) z⁻ⁿ/n)`,
  `e_α e^β = ε(α,β) e^{α+β}`, `z^α e^β = z^{(α,β)} e^β`, `α(n) = ∑ᵢ αᵢ hᵢ(n)`.
  `E⁺(-α,z)` acts on `∏ h_{k}(-n_k) e^β` by replacing each oscillator by
  `h_k(-n_k) - (α_k, α) z^{-n_k}`, i.e. a sum over the subsets of contracted oscillators
  (`contract`, Python's `mask` loop).  `schur α g` is the coefficient of `z^g` in
  `E⁻(-α,z)𝟏`; on unnormalized monomials it is Python's `creation`:
  `∏ αᵢ^{m}/(n^{m} m!)` for `∏ hᵢ(-n)^{m}`, enumerated directly in sorted order (`monos`).
* Iterate formula for oscillator states (`basisModeAux`, Python `basis_mode` of
  `general_modes_v2`): for `u = hᵢ(-n) b`,
  `u_(m) = ∑_{k<0} C(-k-1, n-1) hᵢ(k) b_(m-n-k) + ∑_{k≥0} C(-k-1, n-1) b_(m-n-k) hᵢ(k)`
  (`Y(h(-n)b, z) = :∂^{(n-1)} h(z) Y(b,z):`), with the generalized binomial `gbinom`.
  The first oscillator of the (sorted) code list is peeled off first, as in Python.

No hypotheses: this file only defines functions and checks small instances.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Oscillator lists -/

/-- Insert a code into a nondecreasing list. -/
def insertCode (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | j :: js => if k ≤ j then k :: j :: js else j :: insertCode k js

/-- Merge the codes of `b` into the nondecreasing list `a`. -/
def mergeOsc (a b : List ℕ) : List ℕ := b.foldr insertCode a

/-! ## Heisenberg modes -/

/-- The annihilation terms of `hᵢ(n)`, `n > 0`, on a code list: remove one oscillator of
level `n`, with factor `n (αᵢ, α_{k%8})`. -/
def annih (i n : ℕ) : List ℕ → List (List ℕ × ℤ)
  | [] => []
  | k :: ks =>
    let rest := (annih i n ks).map fun p => (k :: p.1, p.2)
    if k / 8 + 1 = n then (ks, (n : ℤ) * Mom.pairSimple i (Mom.simple (k % 8))) :: rest
    else rest

/-- The Heisenberg mode `hᵢ(m)` on a Fock monomial (Python `heis`). -/
def heis (i : ℕ) (m : ℤ) (s : State) : Vec :=
  if m = 0 then addTerm s (Mom.pairSimple i s.1 : ℚ) []
  else if m < 0 then [((s.1, insertCode (i + 8 * ((-m).toNat - 1)) s.2), 1)]
  else normalize ((annih i m.toNat s.2).map fun p => ((s.1, p.1), (p.2 : ℚ)))

/-! ## Vertex operators of `e^α` -/

/-- The nonempty suffixes of a list. -/
def suffixes : List ℕ → List (List ℕ)
  | [] => []
  | k :: ks => (k :: ks) :: suffixes ks

/-- The nondecreasing code lists of level sum `rem` with codes from the ascending candidate
list `cs`, in lexicographic order (depth-first; `fuel ≥ rem` suffices). -/
def monos : ℕ → ℕ → List ℕ → List (List ℕ)
  | _, 0, _ => [[]]
  | 0, _ + 1, _ => []
  | fuel + 1, rem + 1, cs =>
    (suffixes cs).flatMap fun
      | [] => []
      | k :: ks =>
        if k / 8 + 1 ≤ rem + 1 then
          (monos fuel (rem + 1 - (k / 8 + 1)) (k :: ks)).map (k :: ·)
        else []

/-- Numerator `∏ α_{k%8}` and denominator `∏ n_k · m` of `∏_{runs (k, m)} (α_{k%8}/n_k)^m/m!`
for a sorted code list, run by run (`prev`, `mult`: the previous code and its multiplicity so
far).  Integer arithmetic only; one rational division per monomial (`schur`). -/
def coeffAux (α : Mom) : ℕ → ℕ → List ℕ → ℤ × ℕ
  | _, _, [] => (1, 1)
  | prev, mult, k :: ks =>
    let m := if k = prev then mult + 1 else 1
    let r := coeffAux α k m ks
    (α.coord (k % 8) * r.1, (k / 8 + 1) * m * r.2)

/-- The Schur coefficient `S_g`: the coefficient of `z^g` in
`E⁻(-α,z)𝟏 = exp(∑_{n>0} α(-n) zⁿ/n)𝟏`, i.e. `∑ ∏ (αᵢ/n)^{m}/m! ∏ hᵢ(-n)^{m}` over the
unnormalized monomials of grade `g` (Python `creation(α, g)` of `proof_exact4`), on momentum
`0`, sorted. -/
def schur (α : Mom) (g : ℕ) : Vec :=
  (monos g g ((List.range (8 * g)).filter fun k => α.coord (k % 8) ≠ 0)).map fun l =>
    let c := coeffAux α 0 0 l
    ((Mom.zero, l), (c.1 : ℚ) / (c.2 : ℚ))

/-- The contractions of `E⁺(-α,z)` on a code list: for every subset of contracted
oscillators, the remaining (sorted) codes, the product of the factors `-(α_{k%8}, α)`, and the
total level of the contracted oscillators. -/
def contract (α : Mom) : List ℕ → List (List ℕ × ℤ × ℕ)
  | [] => [([], 1, 0)]
  | k :: ks =>
    let r := contract α ks
    let a := -Mom.pairSimple (k % 8) α
    r.map (fun p => (k :: p.1, p.2.1, p.2.2)) ++
      if a = 0 then [] else r.map fun p => (p.1, a * p.2.1, p.2.2 + (k / 8 + 1))

/-- `(e^α)_(m)` on a Fock monomial (Python `vertex`, without the grade ceiling). -/
def vertexOp (α : Mom) (m : ℤ) (s : State) : Vec :=
  let γ := α.add s.1
  let e := Mom.eps α s.1
  let ab := Mom.form α s.1
  (contract α s.2).foldr (fun t acc =>
      let deg : ℤ := -m - 1 - ab + (t.2.2 : ℤ)
      if deg < 0 then acc
      else addVec (smul (e * (t.2.1 : ℚ))
        ((schur α deg.toNat).map fun q => ((γ, mergeOsc t.1 q.1.2), q.2))) acc) []

/-! ## The iterate recursion -/

/-- `a (a-1) ⋯ (a-r+1)`. -/
def descProd (a : ℤ) : ℕ → ℤ
  | 0 => 1
  | r + 1 => descProd a r * (a - r)

/-- The generalized binomial coefficient `C(a, r)` for `a ∈ ℤ`. -/
def gbinom (a : ℤ) (r : ℕ) : ℚ := (descProd a r : ℚ) / (r.factorial : ℚ)

/-- `u_(m) v` for `u = ∏_{k ∈ osc} h_{k%8}(-(k/8+1)) e^α`, by recursion on the code list
(Python `basis_mode` of `general_modes_v2`). -/
def basisModeAux (α : Mom) : List ℕ → ℤ → State → Vec
  | [], m, v => vertexOp α m v
  | k :: ks, m, v =>
    let i := k % 8
    let n := k / 8 + 1
    let target : ℤ := α.norm / 2 + (oscGrade (k :: ks) : ℤ) + (grade v : ℤ) - m - 1
    let neg := (List.range target.toNat).foldr (fun (j : ℕ) acc =>
      let kk : ℤ := -((j : ℤ) + 1)
      addVec (smul (gbinom (-kk - 1) (n - 1))
        (bindVec (basisModeAux α ks (m - (n : ℤ) - kk) v) (heis i kk))) acc) []
    let pos := (List.range (grade v + 1)).foldr (fun (j : ℕ) acc =>
      addVec (smul (gbinom (-(j : ℤ) - 1) (n - 1))
        (bindVec (heis i (j : ℤ) v) (basisModeAux α ks (m - (n : ℤ) - (j : ℤ))))) acc) []
    addVec neg pos

/-- The mode `u_(m) v` of two Fock monomials. -/
def basisMode (u : State) (m : ℤ) (v : State) : Vec := basisModeAux u.1 u.2 m v

/-- The mode `a_(m) b` of two sparse vectors (bilinear extension). -/
def mode (a : Vec) (m : ℤ) (b : Vec) : Vec :=
  bindVec a fun u => bindVec b fun v => basisMode u m v

/-! ## Small checks -/

/-- `E⁻(-α,z)𝟏` at order two for `α = α₀`: `½ h₀(-2) + ½ h₀(-1)²`. -/
example : schur ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ 2 =
    [(S 0 0 0 0 0 0 0 0 [0, 0], 1 / 2), (S 0 0 0 0 0 0 0 0 [8], 1 / 2)] := by
  decide +kernel

/-- `(e^α)_0 e^{-α} = ε(α,-α) α(-1)𝟏 = -h₀(-1)𝟏` for the simple root `α₀`. -/
example : basisMode (S 1 0 0 0 0 0 0 0 []) 0 (S (-1) 0 0 0 0 0 0 0 []) =
    [(S 0 0 0 0 0 0 0 0 [0], -1)] := by
  decide +kernel

/-- `h₀(1) h₀(-1)𝟏 = 2 𝟏`. -/
example : basisMode (S 0 0 0 0 0 0 0 0 [0]) 1 (S 0 0 0 0 0 0 0 0 [0]) = [(vacState, 2)] := by
  decide +kernel

end LatticeVOA
end HaagerupIzumi.C8
