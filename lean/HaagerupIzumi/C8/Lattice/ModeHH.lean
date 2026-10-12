module

public import HaagerupIzumi.C8.Lattice.ModeQR
public import HaagerupIzumi.C8.Lattice.P4Cartan

@[expose] public section

/-!
# A direct evaluator for the modes of quadratic Heisenberg vectors

`ω` is a combination of the states `h_k(-1) h_l(-1) 𝟏` (codes `[k, l]`, `k, l < 8`).  For these,
`basisModeAux` runs its iterate recursion twice; the inner level `(h_l(-1)𝟏)_(m')` is just the
Heisenberg mode `h_l(m')` (`toFock_basisModeAux_one`), so `hhMode k l m v` replaces the inner
recursion by `heis l`.  `basisModeFast` uses it for these states; `modeQRF` is `modeQR` with
`basisModeFast`.  **Link**: `toVQ_modeQRF = modeC`.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem toFock_foldr_bind_vertex_zero_mem (c : ℕ → ℚ) (H : ℕ → Vec) (F : ℕ → ℤ) (l : List ℕ)
    (hF : ∀ j ∈ l, F j ≠ -1) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (H j) (basisModeAux Mom.zero [] (F j)))) acc) []) = 0 := by
  rw [toFock_foldr_addVec]
  refine List.sum_eq_zero fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [toFock_smul, toFock_bindVec]
  have hz : (fun s => toFock (basisModeAux Mom.zero [] (F j) s)) = fun _ => 0 := by
    funext s
    rw [show basisModeAux Mom.zero [] (F j) s = vertexOp Mom.zero (F j) s from rfl,
      toFock_vertexOp_zero, if_neg (hF j hj)]
  rw [hz]
  simp [Finsupp.linearCombination_apply]

theorem annih_eq_nil (i n : ℕ) : ∀ ks : List ℕ, (∀ k ∈ ks, k / 8 + 1 ≠ n) → annih i n ks = []
  | [], _ => rfl
  | k :: ks, h => by
    have ih := annih_eq_nil i n ks fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [annih, ih, List.map_nil, if_neg (h k List.mem_cons_self)]

theorem level_le_oscGrade : ∀ ks : List ℕ, ∀ k ∈ ks, k / 8 + 1 ≤ oscGrade ks
  | [], _, h => absurd h List.not_mem_nil
  | x :: ks, k, h => by
    simp only [oscGrade]
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := level_le_oscGrade ks k h'
      omega

theorem toFock_heis_large (i : ℕ) (m : ℤ) (v : State) (hm : (grade v : ℤ) < m) :
    toFock (heis i m v) = 0 := by
  have hg : oscGrade v.2 ≤ grade v := by simp only [grade]; omega
  have hnil : annih i m.toNat v.2 = [] := annih_eq_nil i m.toNat v.2 fun k hk => by
    have := level_le_oscGrade v.2 k hk
    omega
  unfold heis
  rw [if_neg (by omega), if_neg (by omega), hnil]
  simp [normalize]

/-- `(hᵢ(-1)𝟏)_(m) = hᵢ(m)` on monomials, for every `m`. -/
theorem toFock_basisModeAux_one (i : ℕ) (hi : i < 8) (m : ℤ) (v : State) :
    toFock (basisModeAux Mom.zero [i] m v) = toFock (heis i m v) := by
  have h1 : i % 8 = i := Nat.mod_eq_of_lt hi
  have h2 : i / 8 = 0 := Nat.div_eq_of_lt hi
  have hn0 := Mom.norm_zero'
  rw [basisModeAux.eq_2]
  simp only [h1, h2]
  rcases lt_or_ge m 0 with hm | hm
  · rw [toFock_addVec, toFock_foldr_vertex_single _ _ _ _ _ (-m - 1).toNat List.nodup_range ?_ ?_,
      toFock_foldr_bind_vertex_zero_mem _ _ _ _ ?_, add_zero]
    · have e : -(((-m - 1).toNat : ℕ) + 1 : ℤ) = m := by omega
      simp only [e, gbinom_zero_right, zero_add, Nat.sub_self, one_smul]
    · intro j _ h
      omega
    · rw [List.mem_range]
      simp only [oscGrade, h2]
      omega
    · intro j
      constructor <;> intro h <;> omega
  · rcases le_or_gt m (grade v : ℤ) with hg | hg
    · rw [toFock_addVec, toFock_foldr_vertex_zero_all _ _ _ _ ?_,
        toFock_foldr_bind_vertex_single _ _ _ _ m.toNat List.nodup_range ?_ ?_, zero_add]
      · have e : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
        simp only [e, gbinom_zero_right, zero_add, Nat.sub_self, one_smul]
      · rw [List.mem_range]
        omega
      · intro j
        constructor <;> intro h <;> omega
      · intro j h
        omega
    · rw [toFock_addVec, toFock_foldr_vertex_zero_all _ _ _ _ ?_,
        toFock_foldr_bind_vertex_zero_mem _ _ _ _ ?_, zero_add, toFock_heis_large i m v hg]
      · intro j hj h
        rw [List.mem_range] at hj
        omega
      · intro j h
        omega

/-- `(h_k(-1) h_l(-1) 𝟏)_(m) v` with the inner recursion replaced by `heis l`. -/
def hhMode (k l : ℕ) (m : ℤ) (v : State) : Vec :=
  let target : ℤ := Mom.zero.norm / 2 + (oscGrade [k, l] : ℤ) + (grade v : ℤ) - m - 1
  let neg := (List.range target.toNat).foldr (fun (j : ℕ) acc =>
    let kk : ℤ := -((j : ℤ) + 1)
    addVec (bindVec (heis l (m - 1 - kk) v) (heis k kk)) acc) []
  let pos := (List.range (grade v + 1)).foldr (fun (j : ℕ) acc =>
    addVec (bindVec (heis k (j : ℤ) v) (heis l (m - 1 - (j : ℤ)))) acc) []
  addVec neg pos

theorem toFock_hhMode (k l : ℕ) (hk : k < 8) (hl : l < 8) (m : ℤ) (v : State) :
    toFock (basisModeAux Mom.zero [k, l] m v) = toFock (hhMode k l m v) := by
  have h1 : k % 8 = k := Nat.mod_eq_of_lt hk
  have h2 : k / 8 = 0 := Nat.div_eq_of_lt hk
  have hfun : ∀ m' : ℤ, (fun s => toFock (basisModeAux Mom.zero [l] m' s)) =
      fun s => toFock (heis l m' s) := fun m' => funext fun s => toFock_basisModeAux_one l hl m' s
  rw [basisModeAux.eq_2]
  simp only [h1, h2, hhMode]
  rw [toFock_addVec, toFock_addVec, toFock_foldr_addVec, toFock_foldr_addVec, toFock_foldr_addVec,
    toFock_foldr_addVec]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro j _
    rw [toFock_smul, toFock_bindVec, toFock_bindVec, toFock_basisModeAux_one l hl]
    simp [gbinom_zero_right]
  · congr 1
    apply List.map_congr_left
    intro j _
    rw [toFock_smul, toFock_bindVec, toFock_bindVec, hfun]
    simp [gbinom_zero_right]

/-- `basisMode` with the direct evaluator for quadratic Heisenberg states. -/
def basisModeFast (u : State) (m : ℤ) (v : State) : Vec :=
  match u with
  | (a, [k, l]) => if a = Mom.zero ∧ k < 8 ∧ l < 8 then hhMode k l m v else basisMode u m v
  | _ => basisMode u m v

theorem toV_basisModeFast (u : State) (m : ℤ) (v : State) :
    toV (basisModeFast u m v) = toV (basisMode u m v) := by
  obtain ⟨a, osc⟩ := u
  unfold toV
  match osc with
  | [k, l] =>
    simp only [basisModeFast]
    split_ifs with h
    · obtain ⟨rfl, hk, hl⟩ := h
      rw [← toFock_hhMode k l hk hl]
      rfl
    · rfl
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- `modeQR` with `basisModeFast`. -/
def modeQRF (a : Vec) (m : ℤ) (b : QVec) : QVec :=
  a.flatMap fun p => b.flatMap fun q => liftR (smulR p.2 q.2) (basisModeFast p.1 m q.1)

theorem toVQ_modeQRF_single {s : State} (hs : Valid s) (c : ℚ) (m : ℤ) :
    ∀ b : QVec, (∀ q ∈ b, Valid q.1) →
      toVQ (b.flatMap fun q => liftR (smulR c q.2) (basisModeFast s m q.1)) =
        (c : ℂ) • modeC m (toV [(s, 1)]) (toVQ b)
  | [], _ => by simp [toVQ_nil]
  | q :: b, hb => by
    have ih := toVQ_modeQRF_single hs c m b fun r hr => hb r (List.mem_cons_of_mem _ hr)
    rw [List.flatMap_cons, toVQ_append, ih, toVQ_liftR, toV_basisModeFast, toVQ_cons, map_add,
      map_smul, modeC_single_states hs (hb q List.mem_cons_self), toC_smulR, smul_add, smul_smul]

/-- **Link**: `modeQRF` computes `modeC` on vectors of canonical states. -/
theorem toVQ_modeQRF (m : ℤ) : ∀ (a : Vec) (b : QVec), (∀ p ∈ a, Valid p.1) →
    (∀ q ∈ b, Valid q.1) → toVQ (modeQRF a m b) = modeC m (toV a) (toVQ b)
  | [], b, _, _ => by simp [modeQRF, toVQ_nil]
  | (s, c) :: a, b, ha, hb => by
    have hs : Valid s := ha (s, c) List.mem_cons_self
    have ih := toVQ_modeQRF m a b (fun r hr => ha r (List.mem_cons_of_mem _ hr)) hb
    have h1 := toVQ_modeQRF_single hs c m b hb
    simp only [modeQRF] at ih ⊢
    rw [List.flatMap_cons, toVQ_append, h1, ih,
      show toV ((s, c) :: a) = (c : ℂ) • toV [(s, 1)] + toV a by
        rw [← toV_single_state, toV_cons_mk, toV_cons_mk, toV_nil, add_zero],
      map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

#print axioms toVQ_modeQRF

end LatticeVOA
end HaagerupIzumi.C8
