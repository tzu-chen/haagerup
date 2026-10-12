# Generator for lean/HaagerupIzumi/C8/TRUST_BOUNDARY.md
# Usage (from anywhere): python3 lean/tools/trust_boundary/tb_gen.py && python3 lean/tools/trust_boundary/tb_check.py
# Each entry: (key, loc, ptag, paper, stmt, cite, lattice, other_tags, kind)
# ptag in {E (external), C (certificate), M (manuscript step), D (definitional), S (standard)}
# kind: 'P' = hypothesis (a proposition), 'B' = bundle header (counted as hypothesis too, its
# content listed in sub-entries)
import json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
C8DIR = os.path.normpath(os.path.join(HERE, '..', '..', 'HaagerupIzumi', 'C8'))
# tb_linemap.json maps the line numbers written below (snapshot of 4 October 2026, 14:15 CDT,
# before the audit fixes) to the current files; produced once by tb_map.py.
LINEMAP = {f: {int(k): v for k, v in m.items()} for f, m in json.load(open(os.path.join(HERE, 'tb_linemap.json'))).items()}
_REF = re.compile(r'(?<![\w/])([A-Za-z0-9]+\.lean):((?:\d+(?:–\d+)?)(?:, \d+(?:–\d+)?)*)')
def remap(text):
    # translate pre-fix line numbers of the edited ProofMap files into current ones
    def one(m):
        f, nums = m.group(1), m.group(2)
        if f not in LINEMAP: return m.group(0)
        mp = LINEMAP[f]
        def rng(r):
            return '–'.join(str(mp[int(x)]) for x in r.split('–'))
        return f + ':' + ', '.join(rng(r) for r in nums.split(', '))
    return _REF.sub(one, text)
def ln(f, pat):
    # current line of the first line of C8/f containing pat (for references that must not go stale)
    for i, l in enumerate(open(os.path.join(C8DIR, f)).read().split('\n'), 1):
        if pat in l:
            return f'{f}\u2060:{i}'
    raise ValueError((f, pat))
def ln_after(f, anchor, pat):
    # current line of the first line containing pat after the first line containing anchor
    seen = False
    for i, l in enumerate(open(os.path.join(C8DIR, f)).read().split('\n'), 1):
        if anchor in l: seen = True
        if seen and pat in l:
            return f'{f}\u2060:{i}'
    raise ValueError((f, anchor, pat))
LATDIS = set()  # keys of entries discharged in `lattice_proof_map` (ProofMapLattice.lean)
E = []
def add(key, loc, ptag, paper, stmt, cite, lattice='—', other='', kind='P', new=False):
    if new:  # current line numbers: protect them from the global remap at the end
        loc, stmt, cite, lattice, other = (x.replace('.lean:', '.lean\u2060:') for x in (loc, stmt, cite, lattice, other))
    E.append(dict(key=key, loc=loc, ptag=ptag, paper=paper, stmt=stmt, cite=cite,
                  lattice=lattice, other=other, kind=kind))

PMC = 'ProofMapConcrete.lean'
BND = 'ProofMapConcreteBoundary.lean'
CHR = 'ProofMapConcreteCharacters.lean'
PF = 'ProofMapConcretePF13.lean'
REG = 'ProofMapConcreteRegularity.lean'
TOP = 'ProofMapConcreteTopBound.lean'
BRB = 'ProofMapConcreteBranching.lean'
BRH = 'ProofMapConcreteBranchH.lean'
VAC = 'ProofMapConcreteVacuum.lean'
RK4 = 'ProofMapConcreteRankFour.lean'
VOA = 'ProofMapConcreteRankFourVoa.lean'
NET = 'ProofMapConcreteNetCount.lean'
UNT = 'ProofMapConcreteUntwisted.lean'
SIM = 'ProofMapSimples.lean'
PMP = 'ProofMap.lean'
EHS = 'Fusion/EndHSchur.lean'
VTZ = 'Regularity/VacuumTopZero.lean'
SET = 'Properness/Setup.lean'
G4 = 'Properness/Gate4.lean'
G5 = 'Properness/Gate5.lean'
PRP = 'ProofMapProperness.lean'

FLM = 'proved for `latticeD` modulo `FLMBorcherds`'
LPM = 'discharged in `lattice_proof_map`'
L_OM = ln('Lattice/S2Link.lean', 'theorem omegaV_mem_S2span')
L_UM = ln('Lattice/S2Link.lean', 'theorem uV_mem_S2span')
L_LEU = ln('Lattice/S2Link.lean', 'theorem S2span_le_U')
L_MG = ln('Lattice/S2Link.lean', 'theorem minimalGeneration_latticeD')
L_DIM = ln('Lattice/S2Link.lean', 'theorem certDimensions_latticeD')
L_FIN = ln('Lattice/S2Link.lean', 'theorem finrank_S2span')
L_EQC = ln('Lattice/S2Closure.lean', 'theorem S2span_eq_closureSpace')
L_CLO = ln('Lattice/S2Closure.lean', 'theorem S2Closed_S2span')
L_PCT = ln('Lattice/PCTLink.lean', 'theorem certPCT_latticeD')
L_TRI = ln('Lattice/P4Link.lean', 'theorem triplet_grade_P4')
L_DP = ln('Lattice/P4Link.lean', 'def latticeDP')
L_HLQ = ln('Lattice/P4Link.lean', 'theorem hL_q_latticeDP')
L_HRP = ln('Lattice/P4Link.lean', 'theorem hR_qp_latticeDP')
L_HR0 = ln('Lattice/P4Link.lean', 'theorem hR_q0_latticeDP')
L_HRM = ln('Lattice/P4Link.lean', 'theorem hR_qm_latticeDP')
L_FLM = ln('Lattice/FLMReduce.lean', 'theorem flmInput_of_borcherds')
L_PMC = ln('Lattice/PCTLink.lean', 'def PCTModeCompatible')
L_PMT = ln('Lattice/PCTModes.lean', 'theorem pctModeCompatible :')
L_ELQ = ln('Lattice/P4Left.lean', 'theorem eL_q_latticeDP')
L_FLQ = ln('Lattice/P4Left.lean', 'theorem fL_q_latticeDP')
L_FRP = ln('Lattice/P4RFRP.lean', 'theorem fR_qp_latticeDP')
L_FRZ = ln('Lattice/P4RFRZ.lean', 'theorem fR_q0_latticeDP')
L_FRM = ln('Lattice/P4RFRM.lean', 'theorem fR_qm_latticeDP')
L_ERP = ln('Lattice/P4RERP.lean', 'theorem eR_qp_latticeDP')
L_ER0 = ln('Lattice/P4RDerived.lean', 'theorem eR_q0_latticeDP')
L_ERM = ln('Lattice/P4RDerived.lean', 'theorem eR_qm_latticeDP')
L_L2 = ln('Lattice/P4RL2.lean', 'theorem L2_P4_latticeDP')
L_KS21 = ln('Lattice/KS21.lean', 'theorem KS21_latticeDP')
PML = 'ProofMapLattice.lean'
M_LPM = ln(PML, 'theorem lattice_proof_map')
M_LC = ln(PML, 'theorem lowerCertificate_latD')
M_KK0 = ln(PML, 'theorem KK0_latD')
L_REL = ln('Lattice/Relations.lean', 'theorem left_sl2 ')
M_FC = ln(PML, 'theorem certFiniteClosure_latD')
M_DIM = ln(PML, 'theorem certDimensions_latD')
M_PCT = ln(PML, 'theorem certPCT_latD')
M_PN = ln(PML, 'def pctNodes')
M_PC = ln(PML, 'def PCTCert')
M_PU = ln(PML, 'theorem pctV_mem_U_latD')
M_LR = ln(PML, 'structure LowerRest')
M_LCI = ln(PML, 'structure LatticeClosureInputs')
M_LRI = ln(PML, 'structure LatticeRemainingInputs')

# ---------------------------------------------------------------- RemainingInputs (20)
RI = 'RemainingInputs'
add('RI.C_finiteClosure', f'{PMC}:195 (node {PRP}:69, def {PRP}:39)', 'C', '',
    'The finite closure certificates: `LowerCertificate D`, a Gate 4 certificate with a Gate 5 certificate, '
    'nilpotence of raising/lowering words of length 25 on `S₃`, and `ω ∈ S₂`, `u ∈ S₂`, `S₂ ≤ U` '
    '(sub-entries below)',
    'cert:initial (2023), cert:lower (2253), Gates 4/5 (2264–2265, sec:gate4 2268, sec:gate5 2430), ledger sec:ledger (5236)',
    f'partly, modulo `FLMBorcherds`: the last three conjuncts (`minimalGeneration_latticeD`, {L_MG}) and the nineteen `LowerCertificate` fields `KK0`, `ω_mem`, `KS₂0`, `KS₂1`, `TK`, `KmK`, `hL_q`, `eL_q`, `fL_q`, `hR_qp`, `hR_q0`, `hR_qm`, `eR_qp`, `eR_q0`, `eR_qm`, `fR_qp`, `fR_q0`, `fR_qm`, `L2_P₄` for `latticeDP` ({L_DP}) are theorems, {LPM} (`certFiniteClosure_latD`, {M_FC}); the other 7 `LowerCertificate` fields (`LowerRest`, {M_LR}), Gates 4/5 and nilpotence are not proved (`LatticeClosureInputs`, {M_LCI}).  `S₂` is exactly the closure, all 524 closure relations (`S2span_eq_closureSpace`, {L_EQC}); `dim S₂ = 120` (`finrank_S2span`, {L_FIN}) is proved but not needed by the node',
    kind='B')
add('RI.C_dimensions', f'{PMC}:196 (node {PRP}:70–71)', 'C', '',
    '`dim K = 6`, `dim B₁ = 86`, and `K` is spanned by two commuting standard 𝔰𝔩₂-triples (`IsSl2SumSpan`)',
    'cert:initial (2023–2030); `E₆ ⊕ A₂` lattice: 8 + 72 + 6 = 86',
    f'**{FLM}** (`certDimensions_latticeD`, {L_DIM}; `certDimensions_lattice`, Lattice/VOA.lean:320); {LPM} (`certDimensions_latD`, {M_DIM})')
LATDIS.add('RI.C_dimensions')
add('RI.C_pct', f'{PMC}:197 (node {PMP}:44–45, opaque)', 'C', '',
    'The exact PCT certificate: the transported PCT involution `θ_g` preserves `S₂`',
    'cert:initial (2024), line 2604; transport `θ_g = gθg⁻¹` (1979–1992)',
    f'`θ_g S₂ = S₂` **proved for `latticeD`** (`certPCT_latticeD`, {L_PCT}) modulo `FLMBorcherds`; in `concrete_proof_map` the node `certPCT` is opaque; in `lattice_proof_map` it is `PCTCert` ({M_PC}; `pctNodes`, {M_PN}): `θ_g` mode-compatible (an antilinear automorphism) ∧ `θ_g S₂ = S₂` ∧ `θ_g U = U`, {LPM} (`certPCT_latD`, {M_PCT}) from `pctModeCompatible` ({L_PMT}, a theorem with no hypotheses), `certPCT_latticeD` and `pctV_mem_U_latD` ({M_PU})')
LATDIS.add('RI.C_pct')
add('RI.C_structural', f'{PMC}:198 (nodes {BRB}:139, {PF}:90, {REG}:104)', 'C', '',
    'Conjunction of: the opaque part `R.certStructural` (Potts/PF13 fields, the core `T` and its spectral witnesses, cert:structural-inputs); '
    '`CurrentsIrreducible D u` ({BRB}:74: `B₁/K` has no proper nonzero subspace stable under the zero modes of `U`); '
    '`PF13SelfRow P.A P.L P.a P.b P.d P.c` (`c = 8/5`) ({PF}:51–67: the 16 one-sided OPE identities of the generated pair `L, a`); '
    'and the positive-stress identity `ω = ω_{A₁,₁} + (3403/4563) ω̄_{A₁,₃₉} + (25/6) p̄ + (25/26) z̄` ({REG}:52, 129)'.replace('{BRB}', BRB).replace('{PF}', PF).replace('{REG}', REG),
    'cert:structural-inputs (2645–2682), eq:positive-stress (≈2688), currents 2677–2682, PF13 rows 2660–2667',
    'not proved')
add('RI.C_discriminant', f'{PMC}:199 (node {PMP}:50, opaque)', 'C', '',
    'The discriminant form of the lattice VOA `B` is `(ℤ/3)²` with `q(a,b) = (2a²+b²)/3`, and `H/B` lies on the isotropic line `L₊`',
    'lines 3326–3333', 'not proved (the arithmetic of `q` is in `Data/Weights`)')
add('RI.E_cklw529', f'{PMC}:200 (doc {PMP}:178–184)', 'E', 'Carpi–Kawahigashi–Longo–Weiner',
    'A PCT-stable strongly generated subalgebra of the unitary lattice VOA is a simple unitary VOA of CFT type with `c = 8`, `U₂ = S₂`, `U₃ = S₃`; concrete conjunct `dim U₀ = 1`',
    'CKLW Prop. 5.29; cor:initial-grades (228); `U₂ = S₂, U₃ = S₃` formalized in `InitialGrades.cor_initial_grades_of_certificates`', '—',
    other='[manuscript step] cor:initial-grades content')
add('RI.L_rational', f'{PMC}:201 (doc {PMP}:232–235)', 'M', '',
    '`Rep(U)` rigid and semisimple + `C₂`-cofinite + CFT type ⇒ `U` strongly rational',
    'Theorem thm:positive-stress-rationality (lines 3014–3032)', '—', other='open L arrow')
add('RI.E_dmno', f'{PMC}:202 (doc {PMP}:251–256)', 'E', 'Davydov–Müger–Nikshych–Ostrik',
    '`H` holomorphic ⇒ Lagrangian ⇒ `Rep(U) ≃ Z(𝓕)`, `𝓕 = Rep(U)_H`; concrete conjuncts: the dimensions of `𝓕` form a positive duality-invariant character, `∑ d_i² = 3s`, `d_X = s - 1`',
    'DMNO §4; positive spherical structure from character asymptotics; extension dimension identities (3243–3260)', '—',
    other='[manuscript step] positivity and dimension identities')
add('RI.E_gsy', f'{PMC}:204 (doc {PMP}:332–336)', 'E', 'Gannon–Schopieray–Yadav',
    'An untwisted `HI(ℤ/3)` category with the twelve twists of line 4053 has the standard Haagerup modular data (opaque node `modularData`)',
    'GSY Theorem A(2)/5.1 (lines 4065–4066)', '—')
add('RI.E_netCR', f'{PMC}:206 (doc {PMP}:357–360)', 'E', 'Tener / Longo (nets)',
    '`U` strongly rational, unitary, CFT type ⇒ the net `𝒩_U` is completely rational',
    'Tener [TenFusion] Cor. 4.24; [TenFields] Prop. 7.5, Lemma 7.6; Longo Thm 24 (4271–4279)', '—')
add('RI.L_reconstruction', f'{PMC}:207 (doc {PMP}:372–377)', 'M', '',
    'A3: reconstruction sends the irreducible `𝒩_U` sectors injectively to unitarizable simple `U`-modules (concrete: `recon` injective, values unitarizable)',
    'Prop. clm:analytic-reconstruction (4477–4577); external Henriques–Tener Thms 8.9, 9.5, Cor. 9.7, Rem. 9.8', '—',
    other='open L arrow; [external] Henriques–Tener')
add('RI.L_annulus', f'{PMC}:209 (doc {PMP}:382–391)', 'M', '',
    'A1: pairwise annulus compatibility of the bounded-insertion and smeared-field nets',
    'Prop. clm:analytic-annulus (4621–4864); external Tener [TenFields], Henriques–Tener [HTAnn], [HTNet]', '—',
    other='open L arrow; [external] Tener, Henriques–Tener')
add('RI.E_tener', f'{PMC}:210 (doc {PMP}:392–393)', 'E', 'Tener / Longo (nets)',
    'Strong unitarity + annulus compatibility ⇒ `U` completely unitary (positivity of fusion forms)',
    'Tener, Def. 2.18, Cor. 4.6', '—')
add('RI.L_boundaryUnitary', f'{PMC}:211 (doc {PMP}:395–398)', 'M', '',
    '`U` completely unitary ⇒ `𝓕 = Rep(U)_H` (all modules) is a unitary fusion category',
    'Lemma lem:analytic-unitary-all-modules (4901); external Gui Thms 2.21, 2.28, 3.13; algebraic core in Category/', '—',
    other='open L arrow; [external] Gui')
add('RI.E_izumi', f'{PMC}:212 (doc {PMP}:399–401)', 'E', 'Izumi',
    'A unitary fusion category with ring `HI(ℤ/3)` and untwisted pointed part is `𝓗₂` or `𝓗₃`',
    'Izumi Def. 2.7, Thms 5.9, 9.1; `H²(ℤ/3, ℂˣ) = 0` proved (`Fusion.units_cube_surjective`)', '—')
add('RI.E_moritaCenter', f'{PMC}:213 (doc {PMP}:402–405)', 'E', 'Grossman–Snyder / DMNO / Reutter',
    '`𝓕 ≃ 𝓗₂` or `𝓗₃` + Lagrangian center + complete unitarity ⇒ `Rep(U) ≃ Z(𝓗₃)` as unitary ribbon categories',
    'Grossman–Snyder Thm 1.4; DMNO; Reutter Thm 5', '—')
add('RI.E_netCenter', f'{PMC}:215 (doc {PMP}:406–407)', 'E', 'Grossman–Snyder / DMNO / Reutter',
    'The same identification for the net: `Rep(𝒩_U) ≃ Z(𝓗₃)`', 'Cor. cor:analytic-net-haagerup', '—')
add('RI.E_netExtension', f'{PMC}:216 (doc {PMP}:408–410)', 'E', 'Longo–Rehren / Müger / DMNO',
    'The holomorphic net extension `𝒩_U ⊂ 𝓔₃`', 'Longo–Rehren Thm 4.9; Longo Thm 24; DMNO Cor. 4.1, Prop. 4.4; Müger §§4, 8', '—')
add('RI.E_diagonal', f'{PMC}:217 (doc {PMP}:411–414)', 'E', 'Rehren',
    'The diagonal full net with `Z = ∑ |χ_i|²`', 'Rehren Thm 1.4, Prop. 1.5, Cor. 1.6 (lines 5089–5091)', '—')
add('RI.E_e8Extension', f'{PMC}:219 (doc {PMP}:415–421)', 'E', 'HKL / Gui / ABD / Dong–Mason (E₈)',
    'The chosen `𝓗₃` extension `H′ ≅ V_{E₈}` and its defects', 'DMNO; Huang–Kirillov–Lepowsky Thms 3.2–3.6; Gui Q-systems; Abe–Buhl–Dong Prop. 5.2; Dong–Mason Thm 1; Müger', '—')

# ---------------------------------------------------------------- C_finiteClosure sub-entries
LC = [('KK0', 276, '`K_(0) K ⊆ K`'), ('KS₂0', 277, '`K_(0) S₂ ⊆ S₂`'), ('KS₂1', 278, '`K_(1) S₂ ⊆ K`'),
      ('TK', 279, '`T K ⊆ S₂`'), ('KmK', 280, '`K_(-1) K ⊆ S₂`'), ('ω_mem', 281, '`ω ∈ S₂`'),
      ('S₂S₂0', 282, '`(S₂)_(0) S₂ ⊆ S₃`'), ('S₂S₂1', 283, '`(S₂)_(1) S₂ ⊆ S₂`'), ('S₂S₂2', 284, '`(S₂)_(2) S₂ ⊆ K`'),
      ('N₃_le_S₃', 285, '`N₃ = K₋₁S₂ + TS₂ ⊆ S₃`'), ('S₃_prov', 286, '`S₃ ⊆ N₃ + (S₂)_(0)S₂`'),
      ('P₄_prov', 287, '`P₄ ⊆ (S₂)_(0)S₃ + N₄`'), ('hL_q', 288, '`H_L(0)` kills the triplet `P₄`'), ('eL_q, fL_q', '289–290', '`E_L(0)`, `F_L(0)` kill the triplet `P₄`'),
      ('hR_qp, hR_q0, hR_qm', '291–293', '`H_R(0) q_± = ±2 q_±`, `H_R(0) q₀ = 0`'),
      ('eR_qp', 294, '`E_R(0) q₊ = 0`'), ('eR_q0, eR_qm', '295–296', '`E_R(0) q₀ = 2 q₊`, `E_R(0) q₋ = 2 q₀`'),
      ('fR_qp', 297, '`F_R(0) q₊ = q₀`'), ('fR_q0', 298, '`F_R(0) q₀ = q₋`'), ('fR_qm', 299, '`F_R(0) q₋ = 0`'),
      ('L1_P₄', 300, '`L(1) P₄ ⊆ S₃`'), ('L2_P₄', 301, '`L(2) P₄ ⊆ S₂`')]
CLOS = f'**proved for `latticeD`** (`S2Closed_S2span`, {L_CLO}: the closure conditions of the minimal-generation record, half of `S2span_eq_closureSpace`; with `T x = x_(-2) 𝟏`) modulo `FLMBorcherds`; {LPM} (`lowerCertificate_latD`, {M_LC})'
LCLAT = {'ω_mem': f'**proved for `latticeD`** (`omegaV_mem_S2span`, {L_OM}) modulo `FLMBorcherds`; {LPM} (`lowerCertificate_latD`, {M_LC})',
         'KS₂0': CLOS, 'TK': CLOS, 'KmK': CLOS,
         'KK0': f'**proved for `latticeD`** (`KK0_latD`, {M_KK0}: the kernel-checked current brackets `left_sl2`, `right_sl2`, `left_right_commute`, {L_REL}, for one order of each pair, skew symmetry for the other) modulo `FLMBorcherds`; {LPM}',
         'hL_q': f'**proved for `latticeDP`** (`hL_q_latticeDP`, {L_HLQ}) modulo `FLMBorcherds`; {LPM}',
         'fR_qp': f'**proved for `latticeDP`** (`fR_qp_latticeDP`, {L_FRP}: kernel replay of `F_R(0) q₊ = q₀` for the actual triplet; settles the normalization of `q₀`) modulo `FLMBorcherds`; {LPM}',
         'fR_q0': f'**proved for `latticeDP`** (`fR_q0_latticeDP`, {L_FRZ}: kernel replay of `F_R(0) q₀ = q₋`) modulo `FLMBorcherds`; {LPM}',
         'fR_qm': f'**proved for `latticeDP`** (`fR_qm_latticeDP`, {L_FRM}: kernel replay of `F_R(0) q₋ = 0`) modulo `FLMBorcherds`; {LPM}',
         'eR_qp': f'**proved for `latticeDP`** (`eR_qp_latticeDP`, {L_ERP}: kernel replay of `E_R(0) q₊ = 0`) modulo `FLMBorcherds`; {LPM}',
         'eR_q0, eR_qm': f'**proved for `latticeDP`** (`eR_q0_latticeDP`, `eR_qm_latticeDP`, {L_ER0}, {L_ERM}: from `F_R(0)` on the triplet and the commutator formula `[E_R(0), F_R(0)] = H_R(0)`) modulo `FLMBorcherds`; {LPM}',
         'L2_P₄': f'**proved for `latticeDP`** (`L2_P4_latticeDP`, {L_L2}: `L(2) q ∈ S₂` for the actual triplet; `S2Saved.S2savedSpan_eq`: the saved `r2_*` basis spans the replayed `S₂`) modulo `FLMBorcherds`; {LPM}',
         'KS₂1': f'**proved for `latticeD`** (`KS21_latticeDP`, {L_KS21}: `K_(1) S₂ ⊆ K` on the 120 basis vectors of `S₂`, 720 kernel checks with `modeQRF`, about 320 s of kernel time) modulo `FLMBorcherds`; {LPM}',
         'eL_q, fL_q': f'**proved for `latticeDP`** (`eL_q_latticeDP`, `fL_q_latticeDP`, {L_ELQ}, {L_FLQ}) modulo `FLMBorcherds`; {LPM}',
         'hR_qp, hR_q0, hR_qm': f'**proved for `latticeDP`** (`hR_qp_latticeDP`, `hR_q0_latticeDP`, `hR_qm_latticeDP`, {L_HRP}, {L_HR0}, {L_HRM}) modulo `FLMBorcherds`; {LPM}'}
for n, l, s in LC:
    add(f'LowerCertificate.{n}', f'{SET}:{l}', 'C', '', s, 'cert:lower (2253–2266)', LCLAT.get(n, 'not proved'))
    if n in LCLAT: LATDIS.add(f'LowerCertificate.{n}')
G4F = [('highest, seed, singletSeed', '129–131', 'witness data: the highest-weight vectors of `S₂` and their seeds in `S₃`', ''),
       ('highest_S₂', 132, 'highest vectors lie in `S₂`', ''), ('highest_eL, highest_eR', '133–134', 'they are killed by `e_L`, `e_R`', ''),
       ('seed_S₃, singletSeed_S₃', '135–136', 'seeds lie in `S₃`', ''),
       ('seed_identity', 137, '`a_(0) p ∈ N₄ + P₄` for seeds `p` (the projected identities)', ''),
       ('singlet_premise_L, singlet_premise_R', '138–141', 'singlet recovery premises', ''),
       ('projected_residual', 142, 'the projected residual identity', ''),
       ('raising_span', 144, '`S₃` is spanned by raisings of the seeds', ''),
       ('S₂_decomp', 146, '`S₂ ⊆ span(highest currents) + TK + K₋₁K + ℂω`', '')]
for n, l, s, _ in G4F:
    add(f'Gate4Certificate.{n}', f'{G4}:{l}', 'C', '', s, 'Gate 4, sec:gate4 (2268–2343); ledger 5283–5300', 'not proved',
        kind='W' if n.startswith('highest, seed') else 'P')
G5F = [('e, charged, a₃, p₃, n₃, c₃, chargedSeeds', '334–349', 'witness data'),
       ('e_mem, charged_sub, highest_sub', '336–338', 'the highest vectors are `e` and the charged ones'),
       ('bottom', 339, 'each charged highest vector has a charged bottom (`ChargedBottom`)'),
       ('a₃_mem, p₃_mem', '344–345', 'membership of the distinguished pair'),
       ('bottom₃, n₃_mem, c₃_ne', '346–348', '`a₃_(0) p₃ = c₃ q₋ + n₃` with `n₃ ∈ N₄`, `c₃ ≠ 0`'),
       ('chargedSeeds_S₃, chargedSeeds_mem', '350–351', 'charged seeds in `S₃` with their identities'),
       ('lowering_span', 353, '`S₃` is spanned by lowerings of the charged seeds')]
for n, l, s in G5F:
    add(f'Gate5Certificate.{n}', f'{G5}:{l}', 'C', '', s, 'Gate 5, sec:gate5 (2430–2600)', 'not proved',
        kind='W' if n.startswith('e, charged') else 'P')
add('certFiniteClosure: raising nilpotence', f'{PRP}:41–42', 'C', '',
    'every word of length 25 in `e_L,(0)`, `e_R,(0)` kills `S₃`', 'Gate 4 (2268–2343)', 'not proved')
add('certFiniteClosure: lowering nilpotence', f'{PRP}:43–44', 'C', '',
    'every word of length 25 in `f_L,(0)`, `f_R,(0)` kills `S₃`', 'Gate 5', 'not proved')
add('certFiniteClosure: ω ∈ S₂, u ∈ S₂, S₂ ≤ U', f'{PRP}:45', 'C', '',
    '`ω, u ∈ S₂` and `S₂ ⊆ ⟨K, ω, u⟩` (minimal generation)', 'cert:initial, minimal-generation record (2047–2055)',
    f'**{FLM}** (`omegaV_mem_S2span`, `uV_mem_S2span`, `S2span_le_U`: `minimalGeneration_latticeD`, {L_MG}); {LPM} (`certFiniteClosure_latD`, {M_FC})')
LATDIS.add('certFiniteClosure: ω ∈ S₂, u ∈ S₂, S₂ ≤ U')

# ---------------------------------------------------------------- BoundaryInputs
add('BoundaryInputs.hBJ', f'{PMC}:150', 'E', 'Bischoff–Jones',
    'Conditional on `certDiscriminant`: the order-3 automorphism `g` of `H/B` and `g⁻¹` have Bischoff–Jones expansions `x, y` (`AutExpansion`, sub-entries)',
    'Lemma lem:automorphisms-invertibles (3273–3296); BJ Lemma 3.1, Cor. 3.4', '—', kind='B')
for pre, use in [('AutExpansion[B]', 'BoundaryInputs.hBJ'), ('AutExpansion[Bn]', 'NetInputs.bj')]:
    add(f'{pre}.hx', f'{BND}:534', 'M', '', '`f ∗ f = f` for algebra automorphisms: the coefficients of `g` are `0` or `d_a`',
        'lines 3283–3285', '—', other='[external] BJ: primitive convolution idempotents are `d_a[a]`')
    add(f'{pre}.hy', f'{BND}:536', 'M', '', 'the same for `g⁻¹`', 'lines 3283–3285', '—', other='[external] BJ')
    add(f'{pre}.hxy', f'{BND}:538', 'E', 'Bischoff–Jones', 'composition is fusion multiplication: `x · y = [𝟙]` (`g ∘ g⁻¹ = id`)', 'BJ Lemma 3.1, Cor. 3.4', '—')
    add(f'{pre}.hxx', f'{BND}:540', 'E', 'Bischoff–Jones', '`x · x = y` (`g ∘ g = g⁻¹`)', 'BJ Lemma 3.1, Cor. 3.4', '—')
    add(f'{pre}.hgid', f'{BND}:542', 'D', '', '`g ≠ id`: `x ≠ [𝟙]`', 'definitional', '—')
    add(f'{pre}.hxa', f'{BND}:544', 'D', '', '`a` is the invertible attached to `g`: `x_a ≠ 0`', 'definitional', '—')
add('BoundaryInputs.simple1, simpleX, simpleY', f'{PMC}:159–161', 'M', '',
    '`𝟙 = U`, `X`, `Y` are simple objects of `𝒞 = Rep(U)`', 'eq:B-branching, eq:H-branching-fork (3219, 3233)', '—')
add('BoundaryInputs.ne1X, ne1Y, neXY', f'{PMC}:164–166', 'M', '',
    '`𝟙, X, Y` are pairwise non-isomorphic (distinct lowest weights `0, 1, 1` and top dimensions `1, 80, 81`)', 'line 3237', '—')
add('BoundaryInputs.bj', f'{PMC}:170', 'E', 'Bischoff–Jones',
    'At rank six: `End_𝒞(H) ≅ K₀(𝓕) ⊗ ℂ` as unital ℂ-algebras (`BJIso`, {EHS}:209)'.replace('{EHS}', EHS),
    'BJ Cor. 3.4 with Lemma 3.1 (line 3799)', '—')
add('BoundaryInputs.dec', f'{PMC}:173', 'M', '',
    'At rank six (`Y ≅ Y*`): `H ≅ 𝟙 ⊞ X ⊞ Y ⊞ Y` in `Rep(U)`', 'eq:rank-fork, lines 3795–3800', '—')
add('BoundaryInputs.hInd', f'{PMC}:176', 'E', 'Ostrik / Ng–Schauenburg / Vafa',
    'For the rank-six ring with multiplicity `m`: the evaluated center-induction formulas (`InductionFormulas`, sub-entries)',
    'Lemma lem:rank6-induction (3842–3914)', '—', kind='B')
for pre in ['InductionFormulas[B]', 'InductionFormulas[Bn]']:
    add(f'{pre}.codegree_X', f'{BND}:168', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`d_X = Dim 𝓕 / f` for the formal codegree `f = 3 + 3δ⁻²`', 'Ostrik Thms 2.5, 2.13', '—')
    add(f'{pre}.codegree_Y', f'{BND}:171', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`d_Y = Dim 𝓕 / 3`', 'Ostrik; line 3864', '—', other='[manuscript step] `3` is the codegree of the 2-dim representation')
    add(f'{pre}.rootC', f'{BND}:173', 'E', 'Ostrik / Ng–Schauenburg / Vafa', 'the twists of `C₀, C₁, C₂` are roots of unity', 'Vafa', '—')
    add(f'{pre}.root', f'{BND}:175', 'E', 'Ostrik / Ng–Schauenburg / Vafa', 'the residual twists are roots of unity', 'Vafa', '—')
    add(f'{pre}.n_pos', f'{BND}:177', 'M', '', 'the residual central simples have `F(Z_j) = n_j ρ` with `n_j > 0`', 'lines 3870–3906', '—')
    add(f'{pre}.sum_b', f'{BND}:179', 'M', '', '`b₀ + b₁ + b₂ = 3m` (adjunction `[F I(a) : ρ] = 3m`)', 'lines 3877–3880', '—')
    add(f'{pre}.nu1_a', f'{BND}:182', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`∑ d_{C_j} θ_{C_j} = Dim 𝓕 · ν₁(a) = 0`', 'Ng–Schauenburg Thm 4.1', '—', other='[manuscript step] `I(a) = ∑ C_j`')
    add(f'{pre}.nu3_a', f'{BND}:185', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`∑ d_{C_j} θ_{C_j}³ = Dim 𝓕 · ν₃(a)`', 'Ng–Schauenburg Thm 4.1', '—', other='[manuscript step]')
    add(f'{pre}.nu1_ρ', f'{BND}:189', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`∑ [I(ρ):Z] d_Z θ_Z = 0` (with `θ_X = θ_Y = 1`)', 'Ng–Schauenburg Thm 4.1', '—', other='[manuscript step] decomposition of `I(ρ)`')
    add(f'{pre}.nu2_ρ', f'{BND}:194', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`∑ [I(ρ):Z] d_Z θ_Z² = Dim 𝓕 · ν₂(ρ)`', 'Ng–Schauenburg Thm 4.1', '—', other='[manuscript step]')
    add(f'{pre}.eps', f'{BND}:199', 'E', 'Ostrik / Ng–Schauenburg / Vafa', 'the second Frobenius–Schur indicator `ν₂(ρ) = ±1`', 'standard FS-indicator theory', '—')
    add(f'{pre}.center_dim', f'{BND}:202', 'E', 'Ostrik / Ng–Schauenburg / Vafa', '`Dim Z(𝓕) = (Dim 𝓕)²`, summed over the center simples `𝟙, X, Y, C_j, Z_j`', 'lines 3897–3904', '—', other='[manuscript step] completeness of the list')

# ---------------------------------------------------------------- CharacterInputs
add('CharacterInputs.fin', f'{CHR}:302', 'E', 'Dong–Lin–Ng', 'conditional on `stronglyRational`: the modular representation of `Rep(U)` has finite image', 'DLN Theorem I', '—')
add('CharacterInputs.T_diag', f'{CHR}:305', 'E', 'Zhu / Huang (modularity)', '`σ(T)` is diagonal with entries `e^{2πi(h - c/24)}` (`c = 8`)', 'Huang', '—')
add('CharacterInputs.S_ne', f'{CHR}:309', 'E', 'Zhu / Huang (modularity)', 'Zhu’s `S` is the categorical `S`, so `S_{0,c₁} = d_{c₁}/D ≠ 0`', 'Huang', '—')
add('CharacterInputs.hol', f'{CHR}:311', 'E', 'Zhu / Huang (modularity)', 'the twelve characters are holomorphic on `ℍ`', 'Zhu', '—')
add('CharacterInputs.cov', f'{CHR}:313', 'E', 'Zhu / Huang (modularity)', 'the character vector is `σ`-covariant', 'Zhu, Huang', '—')
add('CharacterInputs.qexp', f'{CHR}:318', 'D', '', 'the characters are the `q`-series of the graded dimensions, exponents in `n + t_l - 1/3`', 'definitional (twists from `modularData`, `h ≥ 0` from `projectiveVacuum`)', '—')
add('CharacterInputs.summ', f'{CHR}:321', 'E', 'Zhu / Huang (modularity)', 'absolute convergence of the characters on `ℍ`', 'Zhu', '—')
add('CharacterInputs.below', f'{CHR}:327', 'D', '', '`hw l` is the lowest weight of the module labelled `l`: the graded dimensions vanish below `hw l` (its consequence `a l 0 = 0` for `b, a, c₀` is the premise `hpos` of the character arrow, discharged by `noWeightZero_of_vacuum`)', 'definitional', '—', new=True)
add('CharacterInputs.low', f'{CHR}:332–333', 'D', '', 'conditional on `projectiveVacuum` (concrete: `VacuumNode`, `h ≥ 0`) and `modularData` (the twists): the lowest weight `hw l` is one of the exponents `n + t_l` and its coefficient is the top dimension `td l > 0`', 'definitional; line 4178', '—', other='[external] Huang: twist congruence `hw l ∈ t_l + ℤ` (`θ = e^{2πiL(0)}`)', new=True)
add('CharacterInputs.U1', f'{CHR}:327', 'D', '', 'the `q^{2/3}` coefficient of `ch U` is `dim U₁`', 'definitional', '—')
add('CharacterInputs.EG', f'{CHR}:329', 'E', 'Evans–Gannon', 'conditional on `modularData`: the Evans–Gannon fundamental matrix columns `Ξ₀`, `Ξ₃` (`EvansGannon`, sub-entries)', 'EG §§1.4, 2.4, eq. (2.7) (lines 4161–4170)', '—', kind='B')
EGF = [('hol₀, hol₃', '258–259', '`Ξ₀`, `Ξ₃` are holomorphic'), ('cov₀, cov₃', '260–263', '`Ξ₀`, `Ξ₃` are `σ`-covariant'),
       ('q₀, q₃', '264–267', '`q`-expansions in the exponents `n + t_l - 1/3`'), ('sum₀, sum₃', '268–271', 'absolute convergence at every height'),
       ('pp₃_o, pp₃, pp₃_d3', '272–274', 'principal part of `Ξ₃`: `q^{-7/39}` in the `d₃` coordinate only'),
       ('vac₀, vac₃', '275–276', 'the `q^{2/3}` coefficients of the vacuum coordinates are `6` and `13`'),
       ('table', 277, '`Ξ₀` has the lowest weights and top dimensions of the table at line 4178')]
for n, l, s in EGF:
    add(f'EvansGannon.{n}', f'{CHR}:{l}', 'E', 'Evans–Gannon', s, 'Evans–Gannon §§1.4, 2.4', '—')
add('CharacterInputs.res₁', f'{CHR}:333', 'C', '', 'the lattice modules `(0, ±1)` have weights in `1/3 + ℤ_{≥0}`; each simple summand has its lowest weight among them', 'lines 4198–4205', '—', other='[manuscript step] restriction bookkeeping')
add('CharacterInputs.top₁', f'{CHR}:337', 'C', '', 'the lowest space of `(0, ±1)` has dimension 3 and is the sum of the tops of the weight-1/3 summands', 'lines 4198–4205', '—', other='[manuscript step]')
add('CharacterInputs.res₂', f'{CHR}:340', 'C', '', 'the same for `(±1, 0)`, weights in `2/3 + ℤ_{≥0}`', 'lines 4198–4205', '—', other='[manuscript step]')
add('CharacterInputs.top₂', f'{CHR}:343', 'C', '', 'the same for `(±1, 0)`, lowest space of dimension 27', 'lines 4198–4205', '—', other='[manuscript step]')

# ---------------------------------------------------------------- LI
add('LI.ident (SimpleLabels.ident)', f'{SIM}:40; arg {PMC}:443', 'M', '',
    'conditional on `modularData`: the simple `U`-modules are exactly the twelve modules of the character table (`Simp ≃ Label`); with `LI.hw` it respects the twists (`θ = e^{2πiL(0)}`, `C.hw l ∈ t_l + ℤ`)',
    'GSY consequence, line 4053', '—')
add('LI.hw', f'{SIM}:41', 'D', '', 'the identification preserves lowest weights (`C.hw (ident s) = SD.hw s`)', 'definitional', '—')
add('LI.td', f'{SIM}:54', 'D', '', 'the identification preserves top dimensions (`C.td (ident s) = SD.td s`)', 'definitional', '—', new=True)
add('LI.vac', f'{SIM}:42', 'D', '', 'the identification sends `U` to the label `o`', 'definitional', '—')

# ---------------------------------------------------------------- PF13Inputs
add('PF13Inputs.row\'', f'{PF}:99', 'E', 'Dong–Lam–Yamada / Linshaw', '`K(𝔰𝔩₂,13)` satisfies the same 16 one-sided OPE identities at `c = 8/5`', 'DLY decoupling; Linshaw recursive first rows', '—')
add('PF13Inputs.rab', f'{PF}:102', 'C', '', 'the rows `a_(n) b` are common differential normal polynomials in both algebras', 'cert:structural-inputs item 2 (2660–2667)', 'not proved', other='[external] Linshaw (5.4), (5.7), (A.2)')
add('PF13Inputs.rad', f'{PF}:105', 'C', '', 'the same for the rows `a_(n) d`', 'cert:structural-inputs item 2', 'not proved', other='[external] Linshaw')
add('PF13Inputs.simple', f'{PF}:109', 'M', '', 'the vertex algebra generated by `L, a` inside `U` is simple (PCT stability)', 'lines 2838–2839 (CKLW-type, uncited)', '—')
add('PF13Inputs.simple\'', f'{PF}:111', 'E', 'Dong–Lam–Yamada / Linshaw', '`K(𝔰𝔩₂,13)` is simple', 'standard (parafermion literature)', '—')
add('PF13Inputs.gen', f'{PF}:113', 'D', '', '`A` is generated by `L, a`', 'definitional', '—')
add('PF13Inputs.gen\'', f'{PF}:115', 'E', 'Dong–Lam–Yamada / Linshaw', '`K(𝔰𝔩₂,13)` is generated by `L′, a′`', 'DLY; Linshaw', '—')

# ---------------------------------------------------------------- regularity inputs
add('hf, μ, f (Haar averages)', f'{PMC}:464–465', 'D', '', '`μ i` are probability measures on the compact current group, `f i g = g · (factor conformal vector)` is integrable', 'lines 2688–2721', '—', other='[standard] integrability')
add('hK', f'{PMC}:466', 'S', '', 'orbits of the compact current group are compact', 'standard', '—')
add('hfK', f'{PMC}:466', 'D', '', 'the orbit maps take values in the orbits `St.K i`', 'definitional', '—')
add('havg', f'{PMC}:467', 'D', '', '`St.avg i` is the Haar average `∫ f i dμ i`', 'definitional', '—')
add('hfac', f'{PMC}:468–470', 'E', 'Abe–Buhl–Dong / regularity of the factors', 'conditional on `pf13Factor`: every orbit point has symmetric zero mode whose eigenvectors of energy `> D` lie in `C₂(U)` (`FactorEnergy`)', 'Abe–Buhl–Dong Prop. 5.2; lemma lem:positive-c2 (2846–2888)', '—', other='[manuscript step] complete reducibility of `U`, `C_{2,A}(U) ⊆ C₂(U)`')
add('hnonneg', f'{PMC}:471–473', 'E', 'Abe–Buhl–Dong / regularity of the factors', 'conditional on `pf13Factor`: the four factors have nonnegative lowest weights, zero only for the vacuum (`factorNonneg`, an unmodelled predicate)', 'lines 2719–2721 (no citation in the manuscript)', '—')
add('[∀ n, FiniteDimensional (St.U.grade n)]', f'{PMC}:474', 'D', '', 'the grades of `U` are finite-dimensional', 'definitional (CFT type)', '—')

# ---------------------------------------------------------------- TopBoundInputs
add('TopBoundInputs.mono', f'{TOP}:61', 'M', '', 'conditional on `certStructural`, `pf13Factor`: the core-top charge multiplicities of every lowest space decrease away from 0 (finite-dimensional right 𝔰𝔩₂-representation)', 'lem:compatible-top (2890), core extension 3048–3079', '—', other='[certificate] core extension `A_L ⊂ U`')
add('TopBoundInputs.trace', f'{TOP}:66', 'M', '', 'conditional on `positiveStress`, `certStructural`: eq:top-trace, `W_total = h · D` with the fourteen traces of eq:top-W', 'line 2949, table 3153–3162', '—')
add('TopBoundInputs.pos', f'{TOP}:71', 'D', '', 'the lowest space of a simple module is nonzero', 'definitional', '—')

# ---------------------------------------------------------------- BranchBInputs, SignInputs, hadj, hfp
add('BranchBInputs.int', f'{BRB}:152', 'D', '', '`B` is `ℤ`-graded: the summands of `B↓U` have integral lowest weights', 'definitional', '—')
add('BranchBInputs.vacT', f'{BRB}:155', 'D', '', 'the summand containing `𝟏` is `U`, with weight-one space `U₁`', 'definitional', '—')
add('BranchBInputs.vac_unique', f'{BRB}:158', 'S', '', '`B₀ = ℂ𝟏`: no other summand has weight-zero vectors', 'standard (lattice VOA of CFT type)', '—')
add('BranchBInputs.grade', f'{BRB}:160', 'D', '', '`T j` is the weight-one space of `M_j`', 'definitional', '—')
for n, l, s in [('stable', 164, 'the summands `M_j` are `U`-submodules (zero modes preserve their weight spaces)'),
                ('disj', 166, 'the sum `⊕ M_j` is direct'), ('top', 169, 'a summand of lowest weight one has nonzero top'),
                ('sum', 171, '`B₁ = ⊕_j (M_j)₁`')]:
    add(f'BranchBInputs.{n}', f'{BRB}:{l}', 'E', 'Dong–Li–Mason (complete reducibility)', 'conditional on `stronglyRational`: ' + s, 'complete reducibility over a regular VOA (line 3213)', '—')
add('SignInputs.rlyg', f'{BRB}:359', 'E', 'RLYG', 'a finite-order automorphism of `𝔢₆ ⊕ 𝔞₂` fixes a toral subalgebra of dimension `≥ orbits(σ) + orbits(τ)` for diagram automorphisms `σ` of `E₆`, `τ` of `A₂`', 'RLYG §5.2 (line 3309)', '—')
add('SignInputs.rank', f'{BRB}:364', 'S', '', 'if `B^g = U` then `(B₁)^g = U₁ ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` has toral subalgebras of dimension `≤ 2`', 'lines 3305–3307, 3316–3317', '—')
add('SignInputs.sign', f'{BRB}:369', 'M', '', 'if `X` were invertible, `B = U ⊕ X` would be `ℤ/2`-graded with sign automorphism `g`, `B^g = U`', 'lines 3302–3305', '—')
add('hadj', f'{PMC}:446', 'E', 'Davydov–Müger–Nikshych–Ostrik', 'conditional on `lagrangianCenter`: `rank 𝓕 = dim End_𝒞(H) = ∑_l mult(l)²`', 'DMNO adjunction `FI(𝟙) = ⊕ a ⊗ a*` with Schur (3263–3268)', '—', other='[standard] Schur')
add('hfp', f'{PMC}:447', 'S', '', 'conditional on `stronglyRational`: an object of Frobenius–Perron dimension 1 is invertible (`d_X = 1 ⇒ X` invertible)', 'EGNO §3.3', '—')

# ---------------------------------------------------------------- VacuumInputs
add('VacuumInputs.reg', f'{VAC}:156', 'E', 'Abe–Buhl–Dong / regularity of the factors',
    'conditional on `factorNonneg`: for every orbit point `z` and weak `U`-module `M`, `Ω_{A_z}(M) ≅ ⊕` tops on which `z_(1)` acts by lowest weights `≥ 0` and `z_(0)` kills the weight-zero tops (`ComponentTops`, sub-entries)',
    'proof of lem:compatible-top (2903–2907), vacuum-top step (2951–2954); regularity of the factors (Zhu algebra; uncited in the manuscript)', '—', kind='B')
add('ComponentTops.eqv', f'{VTZ}:292', 'E', 'Abe–Buhl–Dong / regularity of the factors', '`Ω_{A′}(M) ≅ ⨁ₖ T k`, the tops of the simple ordinary summands of `M↓A′`', 'regularity of `A′`', '—')
add('ComponentTops.wt_nonneg', f'{VTZ}:290', 'E', 'Abe–Buhl–Dong / regularity of the factors', 'the lowest weights of the factor are `≥ 0`', 'line 2719', '—')
add('ComponentTops.L0_top', f'{VTZ}:293', 'D', '', '`L^{A′}(0) = e_(1)` acts on the top `T k` by its lowest weight', 'definitional', '—')
add('ComponentTops.Lm1_vac', f'{VTZ}:295', 'E', 'Abe–Buhl–Dong / regularity of the factors', '`L^{A′}(-1) = e_(0)` kills the weight-zero tops (vacuum unique of weight 0, `L(-1)𝟏 = 0`)', 'lines 2951–2954', '—')
add('VacuumInputs.noNeg', f'{VAC}:163', 'E', 'Huang / Miyamoto (finite length)', 'conditional on `c2Cofinite` and the (proved) nonnegativity of lowest weights: a grading-restricted generalized module has no generalized `L(0)`-weight `-m`, `m ≥ 1`', 'Huang; Miyamoto (2959–2961)', '—', other='[standard] composition factors are ordinary')
add('VacuumInputs.labels', f'{VAC}:170', 'D', '', 'conditional on `initialGrades`: each `s : Simp` is the class of a simple module with lowest weight `SD.hw s`, and only `SD.vac` admits a nonzero map from `U`', 'definitional', '—', other='[standard] Schur')

# ---------------------------------------------------------------- rigidity
add('hunit', f'{PMC}:454', 'D', '', '`𝒞` is `Rep(U)` with unit `U`, so `VacuumIsProjective` means `𝟙_𝒞` is projective', 'definitional', '—')
add('hEP', f'{PMC}:455–456', 'E', 'McRae / Etingof–Penneys', 'conditional on `c2Cofinite`, `initialGrades`: if `𝟙` is projective, every object of `Rep(U)` has a dual', 'McRae §§2.3, 3; Etingof–Penneys Thm 1.1; growth/non-negligibility 2992–3006', '—', other='[manuscript step] lines 2992–3006')

# ---------------------------------------------------------------- RankFourInputs
add('RankFourInputs.rule', f'{RK4}:78', 'M', '', 'at rank four with exactly three invertibles, `ρ ⊗ ρ = 𝟙 + a + a* + mρ`', 'lines 3356–3358', '—')
add('RankFourInputs.larson', f'{RK4}:84', 'E', 'Larson', 'conditional on `lagrangianCenter`: `m ∈ {0, 2, 3, 6}`', 'Larson Thm 1.1', '—')
add('RankFourInputs.case2', f'{RK4}:93', 'E', 'EGO / HKL / Dong–Mason (m = 2)', 'conditional on `lagrangianCenter`, `stronglyRational`, `initialGrades`, `VacuumNode`: for `m = 2`, `dim U₁ ≥ 16`', 'EGO Thm 7.1/Cor. 7.4; HKL; Dong–Mason Thm 1 (3364–3480); `dim 𝔢₈^{A₄} ≥ 16` proved', '—', other='[manuscript step] twisted double identified with `Rep(U)` via `Z(𝓕) ≃ Rep(U)` (`lagrangianCenter`)', new=True)
add('RankFourInputs.case3', f'{RK4}:107', 'E', 'Zhu / Huang (even-block modularity)', 'conditional on `lagrangianCenter`, `stronglyRational`, `initialGrades`, `VacuumNode`, `BranchB`, `ν₃ = 1`: VOA-side data of one orientation for `m = 3` (`M3FirstVoa ∨ M3ReverseVoa`, sub-entries)', 'prop:near-group-current-obstructions (3482–3770); the center has the modular data of the near-group double (prop:m3-modular, ≈3451)', '—', other='[manuscript step] choice of orientation; `Z(𝓕) ≃ Rep(U)` (`lagrangianCenter`)', kind='B', new=True)
add('RankFourInputs.case6', f'{RK4}:114', 'E', 'Zhu / Huang (even-block modularity)', 'same premises (including `lagrangianCenter`) for `m = 6`: `M6FirstVoa ∨ M6ReverseVoa` (Table 4 with the 6-dimensional swap-symmetric block `SθE6G6m`)', 'same', '—', other='[manuscript step] choice of orientation; `Z(𝓕) ≃ Rep(U)`', kind='B', new=True)
VOAS = [('M3FirstVoa', {'hfin': 43, 'hσS, hσT': '44–45', 'hVhol, hVcov': '47–48', 'hVq': 50, 'hsupp': 52, 'hsum': 53, 'hvac0': 57, 'hpolarB, hpolarA': '58–59', 'hother': 60, 'hvac': 62}, 'Table 1, `d = 15 + A + 10B`'),
        ('M3ReverseVoa', {'hfin': 71, 'hσS, hσT': '72–73', 'hVhol, hVcov': '75–76', 'hVq': 78, 'hsupp': 80, 'hsum': 82, 'hvac0': 85, 'hpolar': 86, 'hother': 87, 'hvac1': 89}, 'Table 2, `d = 14 + 42A`'),
        ('M6FirstVoa', {'hfin': 98, 'hσS, hσT': '99–100', 'hVhol, hVcov': '102–103', 'hVq': 105, 'hsupp': 107, 'hsum': 108, 'hvac0': 111, 'hpolar': 112, 'hother': 113, 'hvac': 114}, 'Table 3, `d = 8 + A`'),
        ('M6ReverseVoa', {'hfin': 123, 'hσS, hσT': '124–125', 'hVhol, hVcov': '127–128', 'hVq': 130, 'hsupp': 132, 'hsum': 133, 'hvac0': 136, 'hpolar': 137, 'hother': 138, 'hvac1': 139}, 'Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`')]
for nm, F, tab in VOAS:
    for f, l in F.items():
        loc = f'{VOA}:{l}'
        if f == 'hfin':
            add(f'{nm}.hfin', loc, 'C', '', f'{tab}: the representation `σ` (pinned at the explicit Weil-type `S, T`) has finite image, a property of the explicit matrices alone (the Weil-type representation factors through some `SL(2, ℤ/N)`)', 'lines 3772–3774; the `SL₂` relations of the matrices are proved (`Theta.WeilSanityST3`, `sl2_relations_*`), finiteness of the generated group is not', 'not proved', other='[standard] Weil representations factor through a finite quotient')
        elif f.startswith('hσS'):
            add(f'{nm}.{f}', loc, 'E', 'Zhu / Huang (even-block modularity)', f'{tab}: `σ(S)`, `σ(T)` are the explicit even-block matrices (Zhu modularity, Huang’s `S`, comparison with the categorical modular data)', 'Zhu; Huang', '—')
        elif f.startswith('hVhol'):
            add(f'{nm}.{f}', loc, 'E', 'Zhu / Huang (even-block modularity)', f'{tab}: the weight-zero even-block vector `V` is holomorphic and `σ`-covariant', 'Zhu; Huang', '—')
        elif f == 'hVq':
            add(f'{nm}.hVq', loc, 'D', '', f'{tab}: `η⁸ V = ∑ δc(x) qˣ` (the `q`-expansion defining `δc`)', 'definitional', '—')
        elif f == 'hsupp':
            add(f'{nm}.hsupp', loc, 'M', '', f'{tab}: `δc` is supported on `λ + ℕ` for the coset weights `λ`', 'lines 3700–3770', '—')
        elif f == 'hsum':
            add(f'{nm}.hsum', loc, 'E', 'Zhu / Huang (even-block modularity)', f'{tab}: absolute convergence of the expansion', 'Zhu', '—')
        else:
            STM = {('M3FirstVoa', 'hvac0'): '`δc_{(0,0)}(0) = 0`', ('M3FirstVoa', 'hpolarB, hpolarA'): '`δc_{(1,0)}(1/7) = -B`, `δc_{(3,0)}(2/7) = 7 - A` (polar coefficients)',
                   ('M3FirstVoa', 'hother'): 'below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((1,0),1/7)`, `((3,0),2/7)`', ('M3FirstVoa', 'hvac'): '`δc_{(0,0)}(1) = 2(d - 22)`, `d = dim U₁`',
                   ('M3ReverseVoa', 'hvac0'): '`δc_{(0,0)}(0) = 1`', ('M3ReverseVoa', 'hpolar'): '`δc_{(2,1)}(2/21) = -A`',
                   ('M3ReverseVoa', 'hother'): 'below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((2,1),2/21)`', ('M3ReverseVoa', 'hvac1'): '`δc_{(0,0)}(1) = 2d - 94`',
                   ('M6FirstVoa', 'hvac0'): '`δc_{(0,0)}(0) = 0`', ('M6FirstVoa', 'hpolar'): '`δc_{(1,0)}(1/4) = (8 - A)/2`',
                   ('M6FirstVoa', 'hother'): 'below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((1,0),1/4)`', ('M6FirstVoa', 'hvac'): '`δc_{(0,0)}(1) = 2(d - 16)`',
                   ('M6ReverseVoa', 'hvac0'): '`δc_{(0,0)}(0) = 1`', ('M6ReverseVoa', 'hpolar'): '`δc_{(2,1)}(1/6) = -P`',
                   ('M6ReverseVoa', 'hother'): 'below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((2,1),1/6)`', ('M6ReverseVoa', 'hvac1'): '`δc_{(0,0)}(1) = 2d - 94`'}
            add(f'{nm}.{f}', loc, 'M', '', f'{tab}: ' + STM[(nm, f)], 'even-block reading of the characters, lines 3700–3770', '—')

# ---------------------------------------------------------------- SectorInputs (x2), BranchHInputs
for s in ['I₁ (J)', 'I₂ (J²)']:
    add(f'SectorInputs[{s}].cert', f'{BRH}:71 (def {BRH}:61)', 'C', '', 'conditional on `certStructural`: `dim J₁ = 81` and `J₁` is irreducible under the zero modes of `U`', 'cert:structural-inputs; lines 3224–3230', 'not proved')
    add(f'SectorInputs[{s}].int', f'{BRH}:74', 'D', '', '`H` is `ℤ`-graded: integral lowest weights', 'definitional', '—')
    add(f'SectorInputs[{s}].noZero', f'{BRH}:77', 'C', '', 'the mixed sector starts at weight one: no summand of lowest weight 0', 'line 3224', 'not proved')
    add(f'SectorInputs[{s}].grade', f'{BRH}:79', 'D', '', '`T j` is the weight-one space of `M_j`', 'definitional', '—')
    for n, l, t in [('stable', 83, 'the summands are `U`-submodules'), ('disj', 85, 'the sum is direct'), ('top', 88, 'lowest weight one ⇒ nonzero top'), ('sum', 90, '`J₁ = ⊕ (M_j)₁`')]:
        add(f'SectorInputs[{s}].{n}', f'{BRH}:{l}', 'E', 'Dong–Li–Mason (complete reducibility)', 'conditional on `stronglyRational`: ' + t, 'complete reducibility; line 3236', '—')
    add(f'SectorInputs[{s}].td', f'{BRH}:92', 'D', '', 'top dimension of a weight-one summand is `dim (M_j)₁`', 'definitional', '—')
add('BranchHInputs.mult', f'{BRH}:133', 'D', '', '`H↓U = B↓U ⊕ J↓U ⊕ J²↓U`: multiplicities add', 'line 3231', '—')
add('BranchHInputs.vac', f'{BRH}:135', 'D', '', 'the vacuum summand `U` has lowest weight 0', 'definitional (CFT type)', '—')
add('BranchHInputs.tdX', f'{BRH}:137', 'D', '', 'the top dimension of `X` is `dim X₁`', 'definitional', '—')

# ---------------------------------------------------------------- NetInputs
add('NetInputs.dims', f'{NET}:74', 'E', 'Kawahigashi–Longo / CKLW (nets)', 'conditional on `netCompletelyRational`: `𝓕_net` is `C*` (positive dual-invariant dimensions), finite index, `Dim 𝓕_net = 3s`, `d_X = s - 1`', 'Kawahigashi–Longo Prop. 2.3 (4334); lines 4334–4345', '—')
add('NetInputs.rank', f'{NET}:78', 'M', '', 'conditional on `netCompletelyRational` and the algebraic rank-six ring: `rank 𝓕_net = 6`', 'graph reduction 4307–4322; center induction 4345–4352', '—', other='[external] center induction')
add('NetInputs.iso', f'{NET}:82', 'E', 'Bischoff–Jones', 'same conditions: `K₀(𝓕_net) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (`FusionAlgebraIso`)', 'BJ Cor. 3.4; eq:analytic-end-algebra (the `End(1⊕X⊕2Y)` step is `Fusion.endHIsoOfSimple`)', '—', other='[manuscript step]')
add('NetInputs.bj', f'{NET}:86', 'E', 'Bischoff–Jones', 'conditional on `certDiscriminant`: BJ expansions of the lattice automorphism on the net inclusion (`AutExpansion[Bn]`, sub-entries above)', 'lines 4355–4358', '—', kind='B')
add('NetInputs.pointed', f'{NET}:91', 'E', 'Kawahigashi–Longo / CKLW (nets)', 'conditional on `netCompletelyRational` and rank six: a pointed `𝓕_net` would give a finite-order automorphism `g` of `B` with `B^g = U`', 'CKLW Thm 6.9, Prop. 7.6, Thm 7.5; index multiplicativity (4362–4373)', '—', other='[manuscript step] index-two extensions 4366–4370')
add('NetInputs.untwisted', f'{NET}:100', 'M', '', '**the conjunct `ν₃(a) = 1` of `NetHI` is assumed**: given the proved node `UntwistedNode` (free-induction equivalence, monoidal equivalence with the untwisted `Vec_{ℤ/3}`), `certDiscriminant`, `netCompletelyRational`', 'lines 4383–4406', '—', other='[standard] FS indicator; lattice-net sector category = `Rep(B)`')
add('NetInputs.ind', f'{NET}:103', 'E', 'Ostrik / Ng–Schauenburg / Vafa', 'the evaluated center-induction formulas for `𝓕_net` (`InductionFormulas[Bn]`, sub-entries above)', 'lines 4410–4424', '—', kind='B')
add('NetInputs.count', f'{NET}:107', 'E', 'Kawahigashi–Longo / CKLW (nets)', 'conditional on `netCompletelyRational`: `#Sec = 6 + #κ` (Lagrangian-algebra theorem and exhaustion of the center simples)', 'line 4426; eq:analytic-center-dimensions', '—', other='[manuscript step] exhaustion')

# ---------------------------------------------------------------- UntwistedInputs, hν
add('UntwistedInputs.hSchur', f'{UNT}:69', 'E', 'Dong / Dong–Lepowsky (lattice modules)', 'conditional on `certDiscriminant`: the nine lattice modules `S v` are simple, pairwise non-isomorphic, `End = ℂ`', 'Dong (lattice VOA modules)', '—')
add('UntwistedInputs.hfusion', f'{UNT}:72', 'E', 'Dong / Dong–Lepowsky (lattice modules)', '`S v ⊗ S w ≅ S (v + w)`', 'Dong–Lepowsky fusion rules', '—')
add('UntwistedInputs.hA', f'{UNT}:75', 'C', '', '`H/B ≅ ⊕_{c ∈ ℤ/3} S (c, c)` (supported on `L₊`)', 'line 3331', 'not proved')
add('UntwistedInputs.hunitS', f'{UNT}:77', 'E', 'Dong / Dong–Lepowsky (lattice modules)', '`S (0, 0) ≅ 𝟙` (the vacuum module `B`)', 'Dong', '—')
add('UntwistedInputs.hS', f'{UNT}:83', 'S', '', '`H/B` is separable (connected étale algebra in a fusion category)', 'standard (Kirillov–Ostrik / DMNO)', '—', other='[external]')
add('UntwistedInputs.h3', f'{UNT}:85', 'S', '', '`3 ≠ 0` in `𝕜`', 'standard', '—')
add('UntwistedInputs.hss', f'{UNT}:88', 'E', 'Dong / Dong–Lepowsky (lattice modules)', '`Rep(B)` is semisimple and pointed: every object is a finite sum of the nine `S v`', 'Dong', '—')
add('UntwistedInputs.hidem', f'{UNT}:93', 'S', '', '`Rep(B)` is idempotent complete (abelian)', 'standard', '—')
add('UntwistedInputs.hθ', ln('ProofMapConcreteUntwisted.lean', '  hθ : disc →'), 'E', 'Dong / Dong–Lepowsky (lattice modules)', 'conditional on `certDiscriminant`: the self-braidings of the three invertibles `S (a, -a)` on `L₋` are trivial (`q = 0` on the isotropic line: trivial twists)', 'lines 3335–3340; braiding of lattice VOA modules', '—', new=True)
add('hν', f'{PMC}:461–463', 'M', '', '**the 𝓕-side content**: given the node `UntwistedNode` (free-induction equivalence and the proved monoidal equivalence `𝒞_{H/B} ≃` untwisted `Vec_{ℤ/3}`), `certDiscriminant`, `lagrangianCenter`, `stronglyRational`, three invertibles: `ν₃(a) = 1`', 'lines 3349–3352 (the tensor embedding into `𝓕` with image `{𝟙, a, a*}`)', '—', other='[standard] Frobenius–Schur indicator of the untwisted `Vec_{ℤ/3}`; the Tannakian (Deligne) step is now proved (`untwisted_vec_equivalence_of_separable`)')

# ---------------------------------------------------------------- structural instance hypotheses
add('𝒞 instances', f'{PMC}:432–434', 'S', '', '`Rep(U)` is a monoidal, preadditive, ℂ-linear category with binary biproducts and kernels, finite-dimensional Hom spaces', 'Huang–Lepowsky–Zhang / McRae (finite tensor category)', '—', other='[external]')
add('Cr instances (and 𝕜)', f'{PMC}:436, 459–460', 'S', '', '`Rep(B)` is a monoidal, preadditive, 𝕜-linear category with finite biproducts, linear monoidal structure, finite-dimensional Homs', 'Dong (lattice VOAs)', '—', other='[external]')
PMCB = 'theorem concrete_proof_map'
add('[BraidedCategory Cr]', ln_after(PMC, PMCB, '[BraidedCategory Cr]'), 'E', 'Dong / Dong–Lepowsky (lattice modules)', '`Rep(B)` is braided (the braiding of lattice VOA modules; Huang for the module category of a rational VOA)', 'lines 3335–3340', '—', new=True)
add('[HasCoequalizers Cr], [PreservesColimits (tensorLeft X)], [PreservesColimits (tensorRight X)]', ln_after(PMC, PMCB, '[HasCoequalizers Cr]'), 'S', '', '`Rep(B)` has coequalizers and `X ⊗ -`, `- ⊗ X` preserve them (a semisimple abelian category with exact tensor product)', 'standard (fusion categories)', '—', new=True)
add('[IsCommMonObj Ah.X]', ln_after(PMC, PMCB, '[IsCommMonObj Ah.X]'), 'E', 'HKL / Gui / ABD / Dong–Mason (E₈)', '`H/B` is a commutative algebra in `Rep(B)` (the extension `B ⊂ H` of VOAs gives a commutative algebra)', 'Huang–Kirillov–Lepowsky; line 3331', '—', new=True)
add('[CharZero k], [CharZero kp]', f'{PMC}:430', 'S', '', 'the fields of the closure data and of the PF13 model have characteristic zero', 'standard', '—')
add('Fintype / DecidableEq instances', f'{PMC}:97–107, 430', 'D', '', 'the index types `ι, κ, Sec, σ, Simp, τ₁, τ₂` are finite with decidable equality', 'definitional', '—', other='[external] `[Fintype Simp]`: finitely many simple modules from `C₂`-cofiniteness (Zhu; Dong–Li–Mason), known before `modularData` (ProofMapSimples.lean\u2060:20–24)')
add('[FiniteDimensional ℝ E], measurable/probability instances', f'{PMC}:100, 464–465', 'D', '', 'the PCT-fixed weight-two space is finite-dimensional; Haar measures are probability measures', 'definitional', '—')

# ============================================================================ rendering
import collections, datetime
TAGNAME = {'E': '[external]', 'C': '[certificate]', 'M': '[manuscript step]', 'D': '[definitional]', 'S': '[standard]'}
def esc(t): return t.replace('|', '\\|')
def nfields(e):
    k = e['key']
    if '…' in k: return 9
    tail = k.split('.', 1)[1] if '.' in k and not k.startswith('certFiniteClosure') else k
    if k.startswith('certFiniteClosure: ω'): return 3
    if k in ('hf, μ, f (Haar averages)',): return 1
    return len([x for x in tail.split(',') if x.strip()])
def row(e, i):
    lat = e['lattice']
    oth = e['other'] or ''
    kind = {'B': ' *(bundle; content listed separately)*', 'W': ' *(witness data, not a hypothesis)*'}.get(e['kind'], '')
    return f"| {i} | `{e['key']}`{kind} | {e['loc']} | {esc(e['stmt'])} | {esc(e['cite'])} | {esc(lat)} | {esc(oth)} |"
HDR = '| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |\n|---|---|---|---|---|---|---|'

out = []
w = out.append
w(open(os.path.join(HERE, 'tb_intro.md')).read())

# Section 4: the 20 RemainingInputs fields
w('\n## 4. The 20 fields of `RemainingInputs` (overview)\n')
w('`RemainingInputs` (ProofMapConcrete.lean:194) holds the arrows of `ProofMap.Inputs` that are not proved for the concrete nodes.  '
  'Each is listed again, with full detail, under its tag in Section 5.\n')
w('| Field | File:line | Tag | One line |\n|---|---|---|---|')
for e in E:
    if e['key'].startswith('RI.'):
        w(f"| `{e['key'][3:]}` | {e['loc']} | {TAGNAME[e['ptag']]} | {esc(e['stmt'])} |")

# Section 5: grouped by tag
w('\n## 5. Every hypothesis, grouped by tag\n')
w('Each hypothesis is listed once, under its primary tag; secondary tags are in the last column.  '
  'Bundles (an input whose content is a structure) are marked and their fields follow as separate entries.  '
  '`AutExpansion` and `InductionFormulas` occur twice (for the boundary category `𝓕`, data `B`, and for the net category `𝓕_net`, data `Bn`); '
  'their fields are listed for each use, as they are separate hypotheses.\n')
order = ['E', 'C', 'M', 'D', 'S']
for t in order:
    es = [e for e in E if e['ptag'] == t]
    w(f"\n### 5.{order.index(t)+1} {TAGNAME[t]} ({sum(1 for e in es if e['kind']=='P')} entries covering {sum(nfields(e) for e in es if e['kind']=='P')} Lean hypotheses; {sum(1 for e in es if e['kind']=='B')} bundles)\n")
    if t == 'E':
        papers = collections.OrderedDict()
        for e in es:
            papers.setdefault(e['paper'], []).append(e)
        for pap, lst in papers.items():
            nh = sum(nfields(e) for e in lst if e['kind']=='P'); nb = sum(1 for e in lst if e['kind']=='B')
            w(f"\n#### {pap} ({nh} {'hypothesis' if nh == 1 else 'hypotheses'}" + (f"; {nb} {'bundle' if nb == 1 else 'bundles'}" if nb else '') + ")\n")
            w(HDR)
            for i, e in enumerate(lst, 1):
                w(row(e, i))
    else:
        w(HDR)
        for i, e in enumerate(es, 1):
            w(row(e, i))

# Section 6: index by structure
w('\n## 6. Index by input structure\n')
w('Every argument of `concrete_proof_map` (ProofMapConcrete.lean:430–477) and every field of its input structures, with the primary tag.\n')
groups = collections.OrderedDict()
STRUCTS = ('LowerCertificate', 'Gate4Certificate', 'Gate5Certificate', 'BoundaryInputs', 'AutExpansion[B]',
           'AutExpansion[Bn]', 'InductionFormulas[B]', 'InductionFormulas[Bn]', 'CharacterInputs', 'EvansGannon', 'LI',
           'PF13Inputs', 'TopBoundInputs', 'BranchBInputs', 'SignInputs', 'VacuumInputs', 'ComponentTops',
           'RankFourInputs', 'M3FirstVoa', 'M3ReverseVoa', 'M6FirstVoa', 'M6ReverseVoa', 'SectorInputs[I₁ (J)]',
           'SectorInputs[I₂ (J²)]', 'BranchHInputs', 'NetInputs', 'UntwistedInputs')
for e in E:
    k = e['key']
    head = k.split('.')[0]
    if k.startswith('RI.'): g = 'RemainingInputs'
    elif k.startswith('certFiniteClosure:'): g = 'C_finiteClosure (other conjuncts)'
    elif '.' in k and head in STRUCTS: g = head
    else: g = 'direct arguments of `concrete_proof_map`'
    e['group'] = g
    groups.setdefault(g, []).append(e)
w('| Structure / argument | Fields (primary tag) |\n|---|---|')
for g, lst in groups.items():
    def short(e):
        if e['group'].startswith('direct') or e['group'].startswith('C_finite'):
            return e['key'].replace('certFiniteClosure: ', '')
        return e['key'].split('.', 1)[1]
    items = ', '.join(f"`{short(e)}` " + ('(data)' if e['kind'] == 'W' else TAGNAME[e['ptag']]) for e in lst)
    w(f'| {g} | {esc(items)} |')

# Section 7: counts
w('\n## 7. Summary counts\n')
P = [e for e in E if e['kind'] == 'P']
B = [e for e in E if e['kind'] == 'B']
c = collections.Counter(e['ptag'] for e in P)
cf = collections.Counter()
for e in P: cf[e['ptag']] += nfields(e)
w('Counting conventions: a *Lean hypothesis* is one proposition-valued argument of `concrete_proof_map` or one '
  'proposition-valued field of an input structure (fields listed together in one row are counted individually; '
  'bundle headers and witness data are not counted, their fields are).  `AutExpansion` and `InductionFormulas` are '
  'counted once per use (for `𝓕` and for `𝓕_net`).  The 20 `RemainingInputs` fields are counted as 19 hypotheses '
  f'plus the bundle `C_finiteClosure`, whose {sum(nfields(e) for e in P if e["key"].split(".")[0] in ("LowerCertificate","Gate4Certificate","Gate5Certificate") or e["key"].startswith("certFiniteClosure"))} certificate fields are counted individually.\n')
w(f'Entries in Section 5: {len(P)} (plus {len(B)} bundle headers); **Lean hypotheses of `concrete_proof_map`: {sum(cf.values())}**.\n')
dis = [e for e in P if e['key'] in LATDIS]
assert len(dis) == len(LATDIS), (LATDIS, [e['key'] for e in dis])
cl = collections.Counter()
for e in dis: cl[e['ptag']] += nfields(e)
ndis = sum(cl.values())
NEWH = {'E': 1}  # FLMBorcherds [external]
GONE = {'S': 1}  # [CharZero k] is not a hypothesis of lattice_proof_map (k = ℂ)
w(f'For `lattice_proof_map` ({M_LPM}) the {ndis} Lean hypotheses of the entries ' + ', '.join(f"`{e['key']}`" for e in dis) +
  ' are theorems (modulo `FLMBorcherds`), and it has one new hypothesis: `hB : FLMBorcherds` **[external]** '
  '(the Borcherds identity for the Fock-model modes, FLM Theorem 8.10.2).  The PCT node needs no input: '
  f'`PCTModeCompatible` ({L_PMC}; `θ_g = pctV`, the map `eq:pct` of lines 1975–1989, is compatible with all modes, an antilinear '
  f'automorphism of the lattice VOA) is the theorem `pctModeCompatible` ({L_PMT}), and the PCT-stability `θ_g U = U` of line '
  '2604 follows (`pctV_mem_U_lattice`); `E_cklw529` still carries Dong–Lin unitarity '
  '(the transported form is positive definite with PCT operator `θ_g`) and CKLW Proposition 5.29.  The instance argument '
  '`[CharZero k]` ([standard], one of the two fields of the entry `[CharZero k], [CharZero kp]`) is not a hypothesis of '
  '`lattice_proof_map`, since `k = ℂ`.\n')
w('| Tag | Lean hypotheses of `concrete_proof_map` | Entries | `RemainingInputs` fields | Lean hypotheses of `lattice_proof_map` |\n|---|---|---|---|---|')
for t in order:
    ri = sum(1 for e in P + B if e['ptag'] == t and e['key'].startswith('RI.'))
    w(f'| {TAGNAME[t]} | {cf[t]} | {c[t]} | {ri} | {cf[t] - cl[t] + NEWH.get(t, 0) - GONE.get(t, 0)} |')
LTOT = sum(cf.values()) - ndis + sum(NEWH.values()) - sum(GONE.values())
w(f'| **total** | **{sum(cf.values())}** | **{len(P)}** | 20 | **{LTOT}** |')
LPMCOUNT = (LTOT, {TAGNAME[t]: cf[t] - cl[t] + NEWH.get(t, 0) - GONE.get(t, 0) for t in order})
ext = collections.Counter()
for e in P:
    if e['ptag'] == 'E': ext[e['paper']] += nfields(e)
w('\n[external] hypotheses by source:\n')
w('| Source | Hypotheses |\n|---|---|')
for k_, v in sorted(ext.items(), key=lambda kv: -kv[1]):
    w(f'| {k_} | {v} |')
lat = [e for e in E if 'proved for `latticeD`' in e['lattice'] or '**proved' in e['lattice'] or e['lattice'].startswith('partly')]
w(f'\nEntries whose statement the lattice model proves, fully or in part (modulo `FLMBorcherds`): {len(lat)} — ' + ', '.join(f"`{e['key']}`" for e in lat) + '.\n')
w(open(os.path.join(HERE, 'tb_outro.md')).read())
open(os.path.join(C8DIR, 'TRUST_BOUNDARY.md'), 'w').write(remap('\n'.join(out)).replace('\u2060', '') + '\n')
print(len(P), len(B), dict(c), dict(cf), sum(cf.values()), 'lattice_proof_map:', LPMCOUNT)
