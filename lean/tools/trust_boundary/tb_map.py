# Reconstruct the pre-fix versions of the edited ProofMap files (reverse edits) and build
# old-line -> new-line maps.
# One-off (4 October 2026): run against the sources right after the audit fixes, it rebuilt the
# pre-fix files by reversing the edits below and wrote tb_linemap.json (pre-fix line -> current
# line).  After later edits of these files its assertions fail by design; keep tb_linemap.json.
import difflib, json, os, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, '..', '..', 'HaagerupIzumi', 'C8')) + '/'
OLD = tempfile.mkdtemp(prefix='tb_old_')
EDITS = {}
EDITS['ProofMapConcreteRankFour.lean'] = [
("""  node `projectiveVacuum`, lines 3370–3372) give a holomorphic `H' ≅ V_{E₈}` with
  `U = H'^{A₄}`; formalized: `Fusion.e8_A4_invariants_ge` (`dim 𝔢₈^{A₄} ≥ 16`). -/
  case2 : rat → init → vac → Fintype.card ι = 4 →""","""  node `projectiveVacuum`, lines 3370–3372) give a holomorphic `H' ≅ V_{E₈}` with
  `U = H'^{A₄}`; the twisted double is identified with `Rep(U)` through the Lagrangian center
  `Z(𝓕) ≃ Rep(U)` (node `lagrangianCenter`, `lag`); formalized: `Fusion.e8_A4_invariants_ge`
  (`dim 𝔢₈^{A₄} ≥ 16`). -/
  case2 : lag → rat → init → vac → Fintype.card ι = 4 →"""),
("""  choice of orientation.  The pole-cancellation identity is **proved** (`Theta.m3_*_obstruction
  _of_voa`).  Uses strict positivity of nonvacuum weights (`vac`), the extension algebra `1 + X`
  and `χ₁ + χ₆₄ = χ_B` (`brB`, lines 3482, 3647) and the untwisted pointed part (`ν₃(a) = 1`). -/
  case3 : rat → init → vac → brB → B.ν₃ = 1 → Fintype.card ι = 4 →""","""  choice of orientation.  The pole-cancellation identity is **proved**
  (`Theta.m3_first_obstruction_of_voa`, `Theta.m3_reverse_obstruction_of_voa`).  Uses the
  Lagrangian center `Z(𝓕) ≃ Rep(U)` (`lag`: the center carries the modular data of the near-group
  double, prop:m3-modular, around line 3451), strict positivity of nonvacuum weights (`vac`), the
  extension algebra `1 + X` and `χ₁ + χ₆₄ = χ_B` (`brB`, lines 3482, 3647) and the untwisted
  pointed part (`ν₃(a) = 1`). -/
  case3 : lag → rat → init → vac → brB → B.ν₃ = 1 → Fintype.card ι = 4 →"""),
]
EDITS['ProofMap.lean'] = [
("""  `near_group_formulas_ne_six` (Theta/; the obstruction theorems are conditional on the applied
  pole-cancellation identity `hcancel`), and `pole_cancellation`.""","""  `near_group_formulas_ne_six` (Theta/; the pole-cancellation identity is proved in
  `Theta.ObstructionsOfVoa`, whose `*_obstruction_of_voa` theorems take the VOA-side data bundled
  in `ProofMapConcreteRankFourVoa`), and `pole_cancellation`."""),
]
EDITS['ProofMapConcreteCharacters.lean'] = [
("""  /-- [definitional] `hw l`, `td l` are the lowest weight and top dimension of `M_l`. -/
  low : ∀ l, (∀ n : ℕ, (n : ℚ) + twistExp l < C.hw l → C.a l n = 0) ∧
    (∃ n : ℕ, (n : ℚ) + twistExp l = C.hw l ∧ C.a l n = C.td l) ∧ 0 < C.td l""",
"""  /-- [definitional] `hw l` is the lowest weight of `M_l`: the coefficients of `ch M_l` below it
  vanish. -/
  below : ∀ l, ∀ n : ℕ, (n : ℚ) + twistExp l < C.hw l → C.a l n = 0
  /-- [definitional] `td l` is the dimension of the top space of `M_l`, which is nonzero; that the
  lowest weight is one of the exponents `t_l + ℤ_{≥0}` of the expansion uses the twist congruence
  `hw l ∈ t_l + ℤ` ([external] Huang, `θ = e^{2πiL(0)}`, node `modularData`) and `hw l ≥ 0` (node
  `projectiveVacuum`). -/
  low : R.projectiveVacuum → R.modularData → ∀ l,
    (∃ n : ℕ, (n : ℚ) + twistExp l = C.hw l ∧ C.a l n = C.td l) ∧ 0 < C.td l"""),
("""  have hlow := H.low
""","""  have hbelow := H.below
  have hlow := H.low hpvR hmd
"""),
("""conditionally on that node of `R` (`modularData`, `stronglyRational`, `certDiscriminant`, and the
opaque parts of `projectiveVacuum`, `initialGrades`).

The index type `Label` of the twelve simple `U`-modules is the one of `Characters`; the combined
file `ProofMapConcrete` uses it also for the top bound and for strong unitarity.
-/""","""conditionally on that node of `R` (`modularData`, `stronglyRational`, `certDiscriminant`,
`projectiveVacuum`, which this file does not override, and the opaque part of `initialGrades`).

The index type `Label` of the twelve labels of the Evans–Gannon table is the one of `Characters`.
The top bound and strong unitarity are stated over the type `Simp` of simple `U`-modules
(`ProofMapSimples`); the combined file `ProofMapConcrete` identifies `Simp` with `Label` by
`SimpleLabels` (conditional on `modularData`).
-/"""),
("""* Remaining inputs: the fields `fin`, `T_diag`, `S_ne`, `hol`, `cov`, `qexp`, `summ`, `low`,
  `U1`, `EG` of `CharacterInputs` (tagged there). -/""","""* Remaining inputs: the fields `fin`, `T_diag`, `S_ne`, `hol`, `cov`, `qexp`, `summ`, `below`,
  `low`, `U1`, `EG` of `CharacterInputs` (tagged there), and `hpos` (no weight-zero vectors in
  `b, a, c₀`, conditional on `modularData` and `projectiveVacuum`; discharged in
  `ProofMapConcrete` by `noWeightZero_of_vacuum`). -/"""),
]
EDITS['ProofMapConcrete.lean'] = [
("""`ProofMapConcreteRigid` (together with the vacuum layer: `regNodes`), `ProofMapConcreteBranching`,
`ProofMapConcreteBranchH`, `ProofMapConcreteRankFour`, `ProofMapConcreteNetCount`,""",
"""`ProofMapConcreteRigid` (together with the vacuum layer: `regNodes`), `ProofMapConcreteBranching`
(which also sets the node `branchH`; `ProofMapConcreteBranchH` has no node function of its own and
proves the arrow `L_branchH` into it), `ProofMapConcreteRankFour`, `ProofMapConcreteNetCount`,"""),
("""`c2Cofinite`, `labels` on `initialGrades`) and the definitional `CharacterInputs.low`; the
rank-four inputs are `RankFourInputs`, conditional on the opaque `lagrangianCenter`,""",
"""`c2Cofinite`, `labels` on `initialGrades`); the character inputs `CharacterInputs` include the
definitional `below`, whose consequence `a l 0 = 0` for `b, a, c₀` is the premise `hpos` of the
character arrow (`noWeightZero_of_vacuum`, from the concrete `VacuumNode` and `LI`); the
rank-four inputs are `RankFourInputs`, conditional on the opaque `lagrangianCenter`,"""),
]
EDITS['ProofMapConcreteRankFourVoa.lean'] = [
("""* a homomorphism `σ : SL(2, ℤ) → GL(E, ℂ)` with `σ(S)`, `σ(T)` the explicit Weil-type matrices
  of the table and with finite image ([external] Zhu modularity of the character vector, Huang's
  identification of `S`, and the comparison with the categorical modular data; finiteness of the
  image is a property of the explicit matrices, lines 3772–3774);""",
"""* a homomorphism `σ : SL(2, ℤ) → GL(E, ℂ)` with `σ(S)`, `σ(T)` the explicit Weil-type matrices
  of the table ([external] Zhu modularity of the character vector, Huang's identification of `S`,
  and the comparison with the categorical modular data) and with finite image (`hfin`,
  [certificate]/[standard]: a property of the explicit matrices alone, since the image is the
  group they generate, a Weil-type representation factoring through a finite quotient
  `SL(2, ℤ/N)`, lines 3772–3774; the `SL₂` relations of the matrices are proved in
  `Theta.WeilSanityST3`, `sl2_relations_*`, the finiteness of the generated group is not
  formalized);"""),
]
EDITS['ProofMapSimples.lean'] = [
("""where label-specific facts are needed (the characters and the strong-unitarity count).
-/""","""where label-specific facts are needed (the characters and the strong-unitarity count).

That `Simp` is finite (`[Fintype Simp]`) and that the lowest weights are rational (`SD.hw : Simp →
ℚ`) are known before `modularData`: [external] `C₂`-cofiniteness (node `c2Cofinite`) gives a
finite-dimensional Zhu algebra, hence finitely many simple ordinary modules (Zhu; Dong–Li–Mason),
whose conformal weights are rational (Dong–Li–Mason; Miyamoto); eq:top-trace (line 2949) shows
directly that they are real and nonnegative.
-/"""),
("""/-- **[manuscript step] The twelve simples after GSY** (Theorem A(2), line 4053; node
`modularData`): the simple `U`-modules are the twelve modules of the character table, i.e. `Simp`
is identified with `Characters.Label`, compatibly with the lowest weights and the vacuum
([definitional]: `C.hw l` is the lowest weight of the module labelled `l`, and `o` labels `U`). -/
structure SimpleLabels {Simp : Type*} (md : Prop) (SD : SimpleData Simp) (C : CharacterData) where
  ident : md → Simp ≃ Label
  hw : ∀ (h : md) (s : Simp), C.hw (ident h s) = SD.hw s
  vac : ∀ h : md, ident h SD.vac = .o""","""/-- **[manuscript step] The twelve simples after GSY** (Theorem A(2), line 4053; node
`modularData`): the simple `U`-modules are the twelve modules of the character table, i.e. `Simp`
is identified with `Characters.Label`, compatibly with the lowest weights, top dimensions and the
vacuum ([definitional]: `C.hw l`, `C.td l` are the lowest weight and top dimension of the module
labelled `l`, and `o` labels `U`).  The identification respects the twists: the label `l` carries
the twist `e^{2πi t_l}` (`t_l = twistExp l`) of the modular data, the module `s` the twist
`e^{2πi SD.hw s}` (`θ = e^{2πiL(0)}`, Huang), and `C.hw l ∈ t_l + ℤ` (`CharacterInputs.low`). -/
structure SimpleLabels {Simp : Type*} (md : Prop) (SD : SimpleData Simp) (C : CharacterData) where
  /-- [manuscript step] GSY Theorem A(2): the simples are the twelve labelled modules. -/
  ident : md → Simp ≃ Label
  /-- [definitional] compatibility with the lowest weights. -/
  hw : ∀ (h : md) (s : Simp), C.hw (ident h s) = SD.hw s
  /-- [definitional] compatibility with the top dimensions. -/
  td : ∀ (h : md) (s : Simp), C.td (ident h s) = SD.td s
  /-- [definitional] the label `o` is the vacuum module `U`. -/
  vac : ∀ h : md, ident h SD.vac = .o"""),
]
MAPS = {}
for f, eds in EDITS.items():
    new = open(BASE + f).read()
    old = new
    for a, b in eds:
        assert old.count(b) == 1, (f, b[:60])
        old = old.replace(b, a)
    open(os.path.join(OLD, f), 'w').write(old)
    ol, nl = old.split('\n'), new.split('\n')
    sm = difflib.SequenceMatcher(None, ol, nl, autojunk=False)
    m = {}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1): m[i1 + k + 1] = j1 + k + 1
        else:
            for k in range(i2 - i1): m[i1 + k + 1] = j1 + min(k, j2 - j1 - 1) + 1 if j2 > j1 else j1
    MAPS[f] = m
json.dump(MAPS, open(os.path.join(HERE, 'tb_linemap.json'), 'w'))
for f, m in MAPS.items():
    shifts = sorted(set((v - k) for k, v in m.items()))
    print(f, len(m), 'shifts', shifts)
