module

public import HaagerupIzumi.C8.Lattice.S2Link
public import HaagerupIzumi.C8.Lattice.PCTRel00
public import HaagerupIzumi.C8.Lattice.PCTRel01
public import HaagerupIzumi.C8.Lattice.PCTRel02
public import HaagerupIzumi.C8.Lattice.PCTRel03
public import HaagerupIzumi.C8.Lattice.PCTRel04
public import HaagerupIzumi.C8.Lattice.PCTRel05
public import HaagerupIzumi.C8.Lattice.PCTRel06
public import HaagerupIzumi.C8.Lattice.PCTRel07
public import HaagerupIzumi.C8.Lattice.PCTRel08
public import HaagerupIzumi.C8.Lattice.PCTRel09
public import HaagerupIzumi.C8.Lattice.PCTRel10
public import HaagerupIzumi.C8.Lattice.PCTRel11
public import HaagerupIzumi.C8.Lattice.PCTRel12
public import HaagerupIzumi.C8.Lattice.PCTRel13
public import HaagerupIzumi.C8.Lattice.PCTRel14
public import HaagerupIzumi.C8.Lattice.PCTRel15
public import HaagerupIzumi.C8.Lattice.PCTRel16
public import HaagerupIzumi.C8.Lattice.PCTRel17
public import HaagerupIzumi.C8.Lattice.PCTRel18
public import HaagerupIzumi.C8.Lattice.PCTRel19
public import HaagerupIzumi.C8.Lattice.PCTRel20
public import HaagerupIzumi.C8.Lattice.PCTRel21
public import HaagerupIzumi.C8.Lattice.PCTRel22
public import HaagerupIzumi.C8.Lattice.PCTRel23
public import HaagerupIzumi.C8.Lattice.PCTRel24
public import HaagerupIzumi.C8.Lattice.PCTRel25
public import HaagerupIzumi.C8.Lattice.PCTRel26
public import HaagerupIzumi.C8.Lattice.PCTRel27
public import HaagerupIzumi.C8.Lattice.PCTRel28
@[expose] public section

/-!
# The PCT certificate: `θ_g S₂ = S₂` for the lattice VOA

Manuscript: certificate `cert:initial` (`c8_expanded_20260929/haagerup_c8_expanded.tex`,
lines 2022–2030: "a PCT-stable 120-dimensional space `S₂`") and line 2604 ("the exact PCT
certificate gives `θ_g S₂ = S₂`"); the map is `eq:pct` (lines 1975–1989), implemented as
`pctV` in `PCTCore.lean` (antilinear, `(-1)^r ∏ c̃ᵢ^{αᵢ}`, `α ↦ -α`, `√-3 ↦ -√-3`).

* `pct_mem_k`: `θ_g r_k ∈ S₂` for the 120 echelon basis vectors `r_k` of the
  minimal-generation record, from the kernel checks `pct_rel_k` (`PCTRel*.lean`: `θ_g r_k`
  equals the recorded combination of the `r_j`) and the semantic link `pctV_toV4`.
* `pctV_mem_S2span`, `pctV_mem_S2span_iff` (`θ_g` is an involution, `pctV_pctV`):
  `θ_g S₂ = S₂`.
* `certPCT_latticeD`: the same for the closure data `latticeD` of `S2Link.lean`, next to
  `certDimensions_latticeD`.
* `pctV_vacV`, `pctV_omegaV`: `θ_g` fixes `𝟏` and `ω`; `pctV_uV_mem`: `θ_g u ∈ S₂`
  (`pct_rel_u`: `θ_g u = (2√13 + 6√-3) r₅₉`).

**Not proved here** (and not assumed by any theorem of this file): that `θ_g` is an antilinear
automorphism of the vertex algebra, `PCTModeCompatible`
(`θ_g (a_(m) b) = (θ_g a)_(m) (θ_g b)`), which the manuscript uses through the transported
unitary structure (`θ_g = g θ g⁻¹`, `θ` the lattice PCT involution).  The certificate proved
here is the finite statement `θ_g S₂ = S₂`.

No hypotheses beyond `FLMInput` (only to have the algebra in `certPCT_latticeD`).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

theorem pct_mem_of_rel {x : Vec4} {cs : List (QA × Vec4)} (h : sort4 (pct4 x) = combo cs)
    (hcs : ∀ p ∈ cs, p.2 ∈ s2basis) (hx : x.AllStates Valid) : pctV (toV4 x) ∈ S2span := by
  rw [pctV_toV4 x hx, ← toV4_sort4, h]
  exact toV4_combo_mem cs fun p hp => s2basis_mem_span _ (hcs p hp)

theorem pct_mem_0 : pctV (toV4 s2r_0) ∈ S2span :=
  pct_mem_of_rel pct_rel_0 (by simp [s2basis]) (s2r_0_states.mono fun _ h => h.1)

theorem pct_mem_1 : pctV (toV4 s2r_1) ∈ S2span :=
  pct_mem_of_rel pct_rel_1 (by simp [s2basis]) (s2r_1_states.mono fun _ h => h.1)

theorem pct_mem_2 : pctV (toV4 s2r_2) ∈ S2span :=
  pct_mem_of_rel pct_rel_2 (by simp [s2basis]) (s2r_2_states.mono fun _ h => h.1)

theorem pct_mem_3 : pctV (toV4 s2r_3) ∈ S2span :=
  pct_mem_of_rel pct_rel_3 (by simp [s2basis]) (s2r_3_states.mono fun _ h => h.1)

theorem pct_mem_4 : pctV (toV4 s2r_4) ∈ S2span :=
  pct_mem_of_rel pct_rel_4 (by simp [s2basis]) (s2r_4_states.mono fun _ h => h.1)

theorem pct_mem_5 : pctV (toV4 s2r_5) ∈ S2span :=
  pct_mem_of_rel pct_rel_5 (by simp [s2basis]) (s2r_5_states.mono fun _ h => h.1)

theorem pct_mem_6 : pctV (toV4 s2r_6) ∈ S2span :=
  pct_mem_of_rel pct_rel_6 (by simp [s2basis]) (s2r_6_states.mono fun _ h => h.1)

theorem pct_mem_7 : pctV (toV4 s2r_7) ∈ S2span :=
  pct_mem_of_rel pct_rel_7 (by simp [s2basis]) (s2r_7_states.mono fun _ h => h.1)

theorem pct_mem_8 : pctV (toV4 s2r_8) ∈ S2span :=
  pct_mem_of_rel pct_rel_8 (by simp [s2basis]) (s2r_8_states.mono fun _ h => h.1)

theorem pct_mem_9 : pctV (toV4 s2r_9) ∈ S2span :=
  pct_mem_of_rel pct_rel_9 (by simp [s2basis]) (s2r_9_states.mono fun _ h => h.1)

theorem pct_mem_10 : pctV (toV4 s2r_10) ∈ S2span :=
  pct_mem_of_rel pct_rel_10 (by simp [s2basis]) (s2r_10_states.mono fun _ h => h.1)

theorem pct_mem_11 : pctV (toV4 s2r_11) ∈ S2span :=
  pct_mem_of_rel pct_rel_11 (by simp [s2basis]) (s2r_11_states.mono fun _ h => h.1)

theorem pct_mem_12 : pctV (toV4 s2r_12) ∈ S2span :=
  pct_mem_of_rel pct_rel_12 (by simp [s2basis]) (s2r_12_states.mono fun _ h => h.1)

theorem pct_mem_13 : pctV (toV4 s2r_13) ∈ S2span :=
  pct_mem_of_rel pct_rel_13 (by simp [s2basis]) (s2r_13_states.mono fun _ h => h.1)

theorem pct_mem_14 : pctV (toV4 s2r_14) ∈ S2span :=
  pct_mem_of_rel pct_rel_14 (by simp [s2basis]) (s2r_14_states.mono fun _ h => h.1)

theorem pct_mem_15 : pctV (toV4 s2r_15) ∈ S2span :=
  pct_mem_of_rel pct_rel_15 (by simp [s2basis]) (s2r_15_states.mono fun _ h => h.1)

theorem pct_mem_16 : pctV (toV4 s2r_16) ∈ S2span :=
  pct_mem_of_rel pct_rel_16 (by simp [s2basis]) (s2r_16_states.mono fun _ h => h.1)

theorem pct_mem_17 : pctV (toV4 s2r_17) ∈ S2span :=
  pct_mem_of_rel pct_rel_17 (by simp [s2basis]) (s2r_17_states.mono fun _ h => h.1)

theorem pct_mem_18 : pctV (toV4 s2r_18) ∈ S2span :=
  pct_mem_of_rel pct_rel_18 (by simp [s2basis]) (s2r_18_states.mono fun _ h => h.1)

theorem pct_mem_19 : pctV (toV4 s2r_19) ∈ S2span :=
  pct_mem_of_rel pct_rel_19 (by simp [s2basis]) (s2r_19_states.mono fun _ h => h.1)

theorem pct_mem_20 : pctV (toV4 s2r_20) ∈ S2span :=
  pct_mem_of_rel pct_rel_20 (by simp [s2basis]) (s2r_20_states.mono fun _ h => h.1)

theorem pct_mem_21 : pctV (toV4 s2r_21) ∈ S2span :=
  pct_mem_of_rel pct_rel_21 (by simp [s2basis]) (s2r_21_states.mono fun _ h => h.1)

theorem pct_mem_22 : pctV (toV4 s2r_22) ∈ S2span :=
  pct_mem_of_rel pct_rel_22 (by simp [s2basis]) (s2r_22_states.mono fun _ h => h.1)

theorem pct_mem_23 : pctV (toV4 s2r_23) ∈ S2span :=
  pct_mem_of_rel pct_rel_23 (by simp [s2basis]) (s2r_23_states.mono fun _ h => h.1)

theorem pct_mem_24 : pctV (toV4 s2r_24) ∈ S2span :=
  pct_mem_of_rel pct_rel_24 (by simp [s2basis]) (s2r_24_states.mono fun _ h => h.1)

theorem pct_mem_25 : pctV (toV4 s2r_25) ∈ S2span :=
  pct_mem_of_rel pct_rel_25 (by simp [s2basis]) (s2r_25_states.mono fun _ h => h.1)

theorem pct_mem_26 : pctV (toV4 s2r_26) ∈ S2span :=
  pct_mem_of_rel pct_rel_26 (by simp [s2basis]) (s2r_26_states.mono fun _ h => h.1)

theorem pct_mem_27 : pctV (toV4 s2r_27) ∈ S2span :=
  pct_mem_of_rel pct_rel_27 (by simp [s2basis]) (s2r_27_states.mono fun _ h => h.1)

theorem pct_mem_28 : pctV (toV4 s2r_28) ∈ S2span :=
  pct_mem_of_rel pct_rel_28 (by simp [s2basis]) (s2r_28_states.mono fun _ h => h.1)

theorem pct_mem_29 : pctV (toV4 s2r_29) ∈ S2span :=
  pct_mem_of_rel pct_rel_29 (by simp [s2basis]) (s2r_29_states.mono fun _ h => h.1)

theorem pct_mem_30 : pctV (toV4 s2r_30) ∈ S2span :=
  pct_mem_of_rel pct_rel_30 (by simp [s2basis]) (s2r_30_states.mono fun _ h => h.1)

theorem pct_mem_31 : pctV (toV4 s2r_31) ∈ S2span :=
  pct_mem_of_rel pct_rel_31 (by simp [s2basis]) (s2r_31_states.mono fun _ h => h.1)

theorem pct_mem_32 : pctV (toV4 s2r_32) ∈ S2span :=
  pct_mem_of_rel pct_rel_32 (by simp [s2basis]) (s2r_32_states.mono fun _ h => h.1)

theorem pct_mem_33 : pctV (toV4 s2r_33) ∈ S2span :=
  pct_mem_of_rel pct_rel_33 (by simp [s2basis]) (s2r_33_states.mono fun _ h => h.1)

theorem pct_mem_34 : pctV (toV4 s2r_34) ∈ S2span :=
  pct_mem_of_rel pct_rel_34 (by simp [s2basis]) (s2r_34_states.mono fun _ h => h.1)

theorem pct_mem_35 : pctV (toV4 s2r_35) ∈ S2span :=
  pct_mem_of_rel pct_rel_35 (by simp [s2basis]) (s2r_35_states.mono fun _ h => h.1)

theorem pct_mem_36 : pctV (toV4 s2r_36) ∈ S2span :=
  pct_mem_of_rel pct_rel_36 (by simp [s2basis]) (s2r_36_states.mono fun _ h => h.1)

theorem pct_mem_37 : pctV (toV4 s2r_37) ∈ S2span :=
  pct_mem_of_rel pct_rel_37 (by simp [s2basis]) (s2r_37_states.mono fun _ h => h.1)

theorem pct_mem_38 : pctV (toV4 s2r_38) ∈ S2span :=
  pct_mem_of_rel pct_rel_38 (by simp [s2basis]) (s2r_38_states.mono fun _ h => h.1)

theorem pct_mem_39 : pctV (toV4 s2r_39) ∈ S2span :=
  pct_mem_of_rel pct_rel_39 (by simp [s2basis]) (s2r_39_states.mono fun _ h => h.1)

theorem pct_mem_40 : pctV (toV4 s2r_40) ∈ S2span :=
  pct_mem_of_rel pct_rel_40 (by simp [s2basis]) (s2r_40_states.mono fun _ h => h.1)

theorem pct_mem_41 : pctV (toV4 s2r_41) ∈ S2span :=
  pct_mem_of_rel pct_rel_41 (by simp [s2basis]) (s2r_41_states.mono fun _ h => h.1)

theorem pct_mem_42 : pctV (toV4 s2r_42) ∈ S2span :=
  pct_mem_of_rel pct_rel_42 (by simp [s2basis]) (s2r_42_states.mono fun _ h => h.1)

theorem pct_mem_43 : pctV (toV4 s2r_43) ∈ S2span :=
  pct_mem_of_rel pct_rel_43 (by simp [s2basis]) (s2r_43_states.mono fun _ h => h.1)

theorem pct_mem_44 : pctV (toV4 s2r_44) ∈ S2span :=
  pct_mem_of_rel pct_rel_44 (by simp [s2basis]) (s2r_44_states.mono fun _ h => h.1)

theorem pct_mem_45 : pctV (toV4 s2r_45) ∈ S2span :=
  pct_mem_of_rel pct_rel_45 (by simp [s2basis]) (s2r_45_states.mono fun _ h => h.1)

theorem pct_mem_46 : pctV (toV4 s2r_46) ∈ S2span :=
  pct_mem_of_rel pct_rel_46 (by simp [s2basis]) (s2r_46_states.mono fun _ h => h.1)

theorem pct_mem_47 : pctV (toV4 s2r_47) ∈ S2span :=
  pct_mem_of_rel pct_rel_47 (by simp [s2basis]) (s2r_47_states.mono fun _ h => h.1)

theorem pct_mem_48 : pctV (toV4 s2r_48) ∈ S2span :=
  pct_mem_of_rel pct_rel_48 (by simp [s2basis]) (s2r_48_states.mono fun _ h => h.1)

theorem pct_mem_49 : pctV (toV4 s2r_49) ∈ S2span :=
  pct_mem_of_rel pct_rel_49 (by simp [s2basis]) (s2r_49_states.mono fun _ h => h.1)

theorem pct_mem_50 : pctV (toV4 s2r_50) ∈ S2span :=
  pct_mem_of_rel pct_rel_50 (by simp [s2basis]) (s2r_50_states.mono fun _ h => h.1)

theorem pct_mem_51 : pctV (toV4 s2r_51) ∈ S2span :=
  pct_mem_of_rel pct_rel_51 (by simp [s2basis]) (s2r_51_states.mono fun _ h => h.1)

theorem pct_mem_52 : pctV (toV4 s2r_52) ∈ S2span :=
  pct_mem_of_rel pct_rel_52 (by simp [s2basis]) (s2r_52_states.mono fun _ h => h.1)

theorem pct_mem_53 : pctV (toV4 s2r_53) ∈ S2span :=
  pct_mem_of_rel pct_rel_53 (by simp [s2basis]) (s2r_53_states.mono fun _ h => h.1)

theorem pct_mem_54 : pctV (toV4 s2r_54) ∈ S2span :=
  pct_mem_of_rel pct_rel_54 (by simp [s2basis]) (s2r_54_states.mono fun _ h => h.1)

theorem pct_mem_55 : pctV (toV4 s2r_55) ∈ S2span :=
  pct_mem_of_rel pct_rel_55 (by simp [s2basis]) (s2r_55_states.mono fun _ h => h.1)

theorem pct_mem_56 : pctV (toV4 s2r_56) ∈ S2span :=
  pct_mem_of_rel pct_rel_56 (by simp [s2basis]) (s2r_56_states.mono fun _ h => h.1)

theorem pct_mem_57 : pctV (toV4 s2r_57) ∈ S2span :=
  pct_mem_of_rel pct_rel_57 (by simp [s2basis]) (s2r_57_states.mono fun _ h => h.1)

theorem pct_mem_58 : pctV (toV4 s2r_58) ∈ S2span :=
  pct_mem_of_rel pct_rel_58 (by simp [s2basis]) (s2r_58_states.mono fun _ h => h.1)

theorem pct_mem_59 : pctV (toV4 s2r_59) ∈ S2span :=
  pct_mem_of_rel pct_rel_59 (by simp [s2basis]) (s2r_59_states.mono fun _ h => h.1)

theorem pct_mem_60 : pctV (toV4 s2r_60) ∈ S2span :=
  pct_mem_of_rel pct_rel_60 (by simp [s2basis]) (s2r_60_states.mono fun _ h => h.1)

theorem pct_mem_61 : pctV (toV4 s2r_61) ∈ S2span :=
  pct_mem_of_rel pct_rel_61 (by simp [s2basis]) (s2r_61_states.mono fun _ h => h.1)

theorem pct_mem_62 : pctV (toV4 s2r_62) ∈ S2span :=
  pct_mem_of_rel pct_rel_62 (by simp [s2basis]) (s2r_62_states.mono fun _ h => h.1)

theorem pct_mem_63 : pctV (toV4 s2r_63) ∈ S2span :=
  pct_mem_of_rel pct_rel_63 (by simp [s2basis]) (s2r_63_states.mono fun _ h => h.1)

theorem pct_mem_64 : pctV (toV4 s2r_64) ∈ S2span :=
  pct_mem_of_rel pct_rel_64 (by simp [s2basis]) (s2r_64_states.mono fun _ h => h.1)

theorem pct_mem_65 : pctV (toV4 s2r_65) ∈ S2span :=
  pct_mem_of_rel pct_rel_65 (by simp [s2basis]) (s2r_65_states.mono fun _ h => h.1)

theorem pct_mem_66 : pctV (toV4 s2r_66) ∈ S2span :=
  pct_mem_of_rel pct_rel_66 (by simp [s2basis]) (s2r_66_states.mono fun _ h => h.1)

theorem pct_mem_67 : pctV (toV4 s2r_67) ∈ S2span :=
  pct_mem_of_rel pct_rel_67 (by simp [s2basis]) (s2r_67_states.mono fun _ h => h.1)

theorem pct_mem_68 : pctV (toV4 s2r_68) ∈ S2span :=
  pct_mem_of_rel pct_rel_68 (by simp [s2basis]) (s2r_68_states.mono fun _ h => h.1)

theorem pct_mem_69 : pctV (toV4 s2r_69) ∈ S2span :=
  pct_mem_of_rel pct_rel_69 (by simp [s2basis]) (s2r_69_states.mono fun _ h => h.1)

theorem pct_mem_70 : pctV (toV4 s2r_70) ∈ S2span :=
  pct_mem_of_rel pct_rel_70 (by simp [s2basis]) (s2r_70_states.mono fun _ h => h.1)

theorem pct_mem_71 : pctV (toV4 s2r_71) ∈ S2span :=
  pct_mem_of_rel pct_rel_71 (by simp [s2basis]) (s2r_71_states.mono fun _ h => h.1)

theorem pct_mem_72 : pctV (toV4 s2r_72) ∈ S2span :=
  pct_mem_of_rel pct_rel_72 (by simp [s2basis]) (s2r_72_states.mono fun _ h => h.1)

theorem pct_mem_73 : pctV (toV4 s2r_73) ∈ S2span :=
  pct_mem_of_rel pct_rel_73 (by simp [s2basis]) (s2r_73_states.mono fun _ h => h.1)

theorem pct_mem_74 : pctV (toV4 s2r_74) ∈ S2span :=
  pct_mem_of_rel pct_rel_74 (by simp [s2basis]) (s2r_74_states.mono fun _ h => h.1)

theorem pct_mem_75 : pctV (toV4 s2r_75) ∈ S2span :=
  pct_mem_of_rel pct_rel_75 (by simp [s2basis]) (s2r_75_states.mono fun _ h => h.1)

theorem pct_mem_76 : pctV (toV4 s2r_76) ∈ S2span :=
  pct_mem_of_rel pct_rel_76 (by simp [s2basis]) (s2r_76_states.mono fun _ h => h.1)

theorem pct_mem_77 : pctV (toV4 s2r_77) ∈ S2span :=
  pct_mem_of_rel pct_rel_77 (by simp [s2basis]) (s2r_77_states.mono fun _ h => h.1)

theorem pct_mem_78 : pctV (toV4 s2r_78) ∈ S2span :=
  pct_mem_of_rel pct_rel_78 (by simp [s2basis]) (s2r_78_states.mono fun _ h => h.1)

theorem pct_mem_79 : pctV (toV4 s2r_79) ∈ S2span :=
  pct_mem_of_rel pct_rel_79 (by simp [s2basis]) (s2r_79_states.mono fun _ h => h.1)

theorem pct_mem_80 : pctV (toV4 s2r_80) ∈ S2span :=
  pct_mem_of_rel pct_rel_80 (by simp [s2basis]) (s2r_80_states.mono fun _ h => h.1)

theorem pct_mem_81 : pctV (toV4 s2r_81) ∈ S2span :=
  pct_mem_of_rel pct_rel_81 (by simp [s2basis]) (s2r_81_states.mono fun _ h => h.1)

theorem pct_mem_82 : pctV (toV4 s2r_82) ∈ S2span :=
  pct_mem_of_rel pct_rel_82 (by simp [s2basis]) (s2r_82_states.mono fun _ h => h.1)

theorem pct_mem_83 : pctV (toV4 s2r_83) ∈ S2span :=
  pct_mem_of_rel pct_rel_83 (by simp [s2basis]) (s2r_83_states.mono fun _ h => h.1)

theorem pct_mem_84 : pctV (toV4 s2r_84) ∈ S2span :=
  pct_mem_of_rel pct_rel_84 (by simp [s2basis]) (s2r_84_states.mono fun _ h => h.1)

theorem pct_mem_85 : pctV (toV4 s2r_85) ∈ S2span :=
  pct_mem_of_rel pct_rel_85 (by simp [s2basis]) (s2r_85_states.mono fun _ h => h.1)

theorem pct_mem_86 : pctV (toV4 s2r_86) ∈ S2span :=
  pct_mem_of_rel pct_rel_86 (by simp [s2basis]) (s2r_86_states.mono fun _ h => h.1)

theorem pct_mem_87 : pctV (toV4 s2r_87) ∈ S2span :=
  pct_mem_of_rel pct_rel_87 (by simp [s2basis]) (s2r_87_states.mono fun _ h => h.1)

theorem pct_mem_88 : pctV (toV4 s2r_88) ∈ S2span :=
  pct_mem_of_rel pct_rel_88 (by simp [s2basis]) (s2r_88_states.mono fun _ h => h.1)

theorem pct_mem_89 : pctV (toV4 s2r_89) ∈ S2span :=
  pct_mem_of_rel pct_rel_89 (by simp [s2basis]) (s2r_89_states.mono fun _ h => h.1)

theorem pct_mem_90 : pctV (toV4 s2r_90) ∈ S2span :=
  pct_mem_of_rel pct_rel_90 (by simp [s2basis]) (s2r_90_states.mono fun _ h => h.1)

theorem pct_mem_91 : pctV (toV4 s2r_91) ∈ S2span :=
  pct_mem_of_rel pct_rel_91 (by simp [s2basis]) (s2r_91_states.mono fun _ h => h.1)

theorem pct_mem_92 : pctV (toV4 s2r_92) ∈ S2span :=
  pct_mem_of_rel pct_rel_92 (by simp [s2basis]) (s2r_92_states.mono fun _ h => h.1)

theorem pct_mem_93 : pctV (toV4 s2r_93) ∈ S2span :=
  pct_mem_of_rel pct_rel_93 (by simp [s2basis]) (s2r_93_states.mono fun _ h => h.1)

theorem pct_mem_94 : pctV (toV4 s2r_94) ∈ S2span :=
  pct_mem_of_rel pct_rel_94 (by simp [s2basis]) (s2r_94_states.mono fun _ h => h.1)

theorem pct_mem_95 : pctV (toV4 s2r_95) ∈ S2span :=
  pct_mem_of_rel pct_rel_95 (by simp [s2basis]) (s2r_95_states.mono fun _ h => h.1)

theorem pct_mem_96 : pctV (toV4 s2r_96) ∈ S2span :=
  pct_mem_of_rel pct_rel_96 (by simp [s2basis]) (s2r_96_states.mono fun _ h => h.1)

theorem pct_mem_97 : pctV (toV4 s2r_97) ∈ S2span :=
  pct_mem_of_rel pct_rel_97 (by simp [s2basis]) (s2r_97_states.mono fun _ h => h.1)

theorem pct_mem_98 : pctV (toV4 s2r_98) ∈ S2span :=
  pct_mem_of_rel pct_rel_98 (by simp [s2basis]) (s2r_98_states.mono fun _ h => h.1)

theorem pct_mem_99 : pctV (toV4 s2r_99) ∈ S2span :=
  pct_mem_of_rel pct_rel_99 (by simp [s2basis]) (s2r_99_states.mono fun _ h => h.1)

theorem pct_mem_100 : pctV (toV4 s2r_100) ∈ S2span :=
  pct_mem_of_rel pct_rel_100 (by simp [s2basis]) (s2r_100_states.mono fun _ h => h.1)

theorem pct_mem_101 : pctV (toV4 s2r_101) ∈ S2span :=
  pct_mem_of_rel pct_rel_101 (by simp [s2basis]) (s2r_101_states.mono fun _ h => h.1)

theorem pct_mem_102 : pctV (toV4 s2r_102) ∈ S2span :=
  pct_mem_of_rel pct_rel_102 (by simp [s2basis]) (s2r_102_states.mono fun _ h => h.1)

theorem pct_mem_103 : pctV (toV4 s2r_103) ∈ S2span :=
  pct_mem_of_rel pct_rel_103 (by simp [s2basis]) (s2r_103_states.mono fun _ h => h.1)

theorem pct_mem_104 : pctV (toV4 s2r_104) ∈ S2span :=
  pct_mem_of_rel pct_rel_104 (by simp [s2basis]) (s2r_104_states.mono fun _ h => h.1)

theorem pct_mem_105 : pctV (toV4 s2r_105) ∈ S2span :=
  pct_mem_of_rel pct_rel_105 (by simp [s2basis]) (s2r_105_states.mono fun _ h => h.1)

theorem pct_mem_106 : pctV (toV4 s2r_106) ∈ S2span :=
  pct_mem_of_rel pct_rel_106 (by simp [s2basis]) (s2r_106_states.mono fun _ h => h.1)

theorem pct_mem_107 : pctV (toV4 s2r_107) ∈ S2span :=
  pct_mem_of_rel pct_rel_107 (by simp [s2basis]) (s2r_107_states.mono fun _ h => h.1)

theorem pct_mem_108 : pctV (toV4 s2r_108) ∈ S2span :=
  pct_mem_of_rel pct_rel_108 (by simp [s2basis]) (s2r_108_states.mono fun _ h => h.1)

theorem pct_mem_109 : pctV (toV4 s2r_109) ∈ S2span :=
  pct_mem_of_rel pct_rel_109 (by simp [s2basis]) (s2r_109_states.mono fun _ h => h.1)

theorem pct_mem_110 : pctV (toV4 s2r_110) ∈ S2span :=
  pct_mem_of_rel pct_rel_110 (by simp [s2basis]) (s2r_110_states.mono fun _ h => h.1)

theorem pct_mem_111 : pctV (toV4 s2r_111) ∈ S2span :=
  pct_mem_of_rel pct_rel_111 (by simp [s2basis]) (s2r_111_states.mono fun _ h => h.1)

theorem pct_mem_112 : pctV (toV4 s2r_112) ∈ S2span :=
  pct_mem_of_rel pct_rel_112 (by simp [s2basis]) (s2r_112_states.mono fun _ h => h.1)

theorem pct_mem_113 : pctV (toV4 s2r_113) ∈ S2span :=
  pct_mem_of_rel pct_rel_113 (by simp [s2basis]) (s2r_113_states.mono fun _ h => h.1)

theorem pct_mem_114 : pctV (toV4 s2r_114) ∈ S2span :=
  pct_mem_of_rel pct_rel_114 (by simp [s2basis]) (s2r_114_states.mono fun _ h => h.1)

theorem pct_mem_115 : pctV (toV4 s2r_115) ∈ S2span :=
  pct_mem_of_rel pct_rel_115 (by simp [s2basis]) (s2r_115_states.mono fun _ h => h.1)

theorem pct_mem_116 : pctV (toV4 s2r_116) ∈ S2span :=
  pct_mem_of_rel pct_rel_116 (by simp [s2basis]) (s2r_116_states.mono fun _ h => h.1)

theorem pct_mem_117 : pctV (toV4 s2r_117) ∈ S2span :=
  pct_mem_of_rel pct_rel_117 (by simp [s2basis]) (s2r_117_states.mono fun _ h => h.1)

theorem pct_mem_118 : pctV (toV4 s2r_118) ∈ S2span :=
  pct_mem_of_rel pct_rel_118 (by simp [s2basis]) (s2r_118_states.mono fun _ h => h.1)

theorem pct_mem_119 : pctV (toV4 s2r_119) ∈ S2span :=
  pct_mem_of_rel pct_rel_119 (by simp [s2basis]) (s2r_119_states.mono fun _ h => h.1)
theorem pctV_basis_mem : ∀ x ∈ s2basis, pctV (toV4 x) ∈ S2span := by
  intro x hx
  simp only [s2basis, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [pct_mem_0, pct_mem_1, pct_mem_2, pct_mem_3, pct_mem_4, pct_mem_5, pct_mem_6, pct_mem_7, pct_mem_8, pct_mem_9, pct_mem_10, pct_mem_11, pct_mem_12, pct_mem_13, pct_mem_14, pct_mem_15, pct_mem_16, pct_mem_17, pct_mem_18, pct_mem_19, pct_mem_20, pct_mem_21, pct_mem_22, pct_mem_23, pct_mem_24, pct_mem_25, pct_mem_26, pct_mem_27, pct_mem_28, pct_mem_29, pct_mem_30, pct_mem_31, pct_mem_32, pct_mem_33, pct_mem_34, pct_mem_35, pct_mem_36, pct_mem_37, pct_mem_38, pct_mem_39, pct_mem_40, pct_mem_41, pct_mem_42, pct_mem_43, pct_mem_44, pct_mem_45, pct_mem_46, pct_mem_47, pct_mem_48, pct_mem_49, pct_mem_50, pct_mem_51, pct_mem_52, pct_mem_53, pct_mem_54, pct_mem_55, pct_mem_56, pct_mem_57, pct_mem_58, pct_mem_59, pct_mem_60, pct_mem_61, pct_mem_62, pct_mem_63, pct_mem_64, pct_mem_65, pct_mem_66, pct_mem_67, pct_mem_68, pct_mem_69, pct_mem_70, pct_mem_71, pct_mem_72, pct_mem_73, pct_mem_74, pct_mem_75, pct_mem_76, pct_mem_77, pct_mem_78, pct_mem_79, pct_mem_80, pct_mem_81, pct_mem_82, pct_mem_83, pct_mem_84, pct_mem_85, pct_mem_86, pct_mem_87, pct_mem_88, pct_mem_89, pct_mem_90, pct_mem_91, pct_mem_92, pct_mem_93, pct_mem_94, pct_mem_95, pct_mem_96, pct_mem_97, pct_mem_98, pct_mem_99, pct_mem_100, pct_mem_101, pct_mem_102, pct_mem_103, pct_mem_104, pct_mem_105, pct_mem_106, pct_mem_107, pct_mem_108, pct_mem_109, pct_mem_110, pct_mem_111, pct_mem_112, pct_mem_113, pct_mem_114, pct_mem_115, pct_mem_116, pct_mem_117, pct_mem_118, pct_mem_119]

/-- **`θ_g S₂ ⊆ S₂`.** -/
theorem pctV_mem_S2span {x : V} (hx : x ∈ S2span) : pctV x ∈ S2span := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact pctV_basis_mem _ (s2basis_getD_mem k)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact S2span.add_mem hy hz
  | smul c y _ hy =>
    rw [pctV_smul]
    exact S2span.smul_mem _ hy

/-- **`θ_g S₂ = S₂`** (`θ_g` is an involution). -/
theorem pctV_mem_S2span_iff (x : V) : pctV x ∈ S2span ↔ x ∈ S2span :=
  ⟨fun h => pctV_pctV x ▸ pctV_mem_S2span h, pctV_mem_S2span⟩

theorem pctV_uV_mem : pctV uV ∈ S2span :=
  pct_mem_of_rel pct_rel_u (by simp [s2basis]) s2u_valid

theorem pctV_vacV : pctV vacV = vacV := by
  have hs : pctValid vacValid = vacValid := Subtype.ext (by decide +kernel)
  have hc : pctCoef vacValid.1 = 1 := by decide +kernel
  rw [vacV, pctV_single, hs, hc, map_one, Rat.cast_one, one_mul]

theorem pctV_omegaV : pctV omegaV = omegaV := by
  have h : pctVec omega = omega := by decide +kernel
  rw [omegaV, pctV_toV omega fun p hp => (omega_states p hp).1, h]

/-- `θ_g` is compatible with all modes (an antilinear vertex-algebra automorphism), as expected
from the manuscript's construction (`θ_g = g θ g⁻¹`).  Proved in `Lattice/PCTModes.lean`
(`pctModeCompatible`, no hypotheses); used in `ProofMap.lattice_proof_map`
(ProofMapLattice.lean) for the PCT node. -/
def PCTModeCompatible : Prop :=
  ∀ (m : ℤ) (a b : V), pctV (modeC m a b) = modeC m (pctV a) (pctV b)

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V)
  (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4)

/-- **The PCT node**: `θ_g S₂ = S₂` for the lattice closure data. -/
theorem certPCT_latticeD :
    ∀ x : V, pctV x ∈ (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ ↔ x ∈ (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ :=
  pctV_mem_S2span_iff

end

#print axioms pctV_mem_S2span
#print axioms pctV_mem_S2span_iff
#print axioms certPCT_latticeD
#print axioms pctV_vacV
#print axioms pctV_omegaV

end LatticeVOA
end HaagerupIzumi.C8
