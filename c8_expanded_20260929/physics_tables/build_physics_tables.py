#!/usr/bin/env python3
"""Typeset existing release data; stdlib only, no VOA or numerical imports.

This is a transcription utility.  It copies finite saved coefficients,
normalizes rational phase encodings, and checks table coverage.  It does
not regenerate lattice products, fusion, characters, or correlators.
Run from any directory.  Original artifacts are opened read-only.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter, defaultdict
import csv
import hashlib
import json
import math

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
SRC = ROOT / 'c8_physics_20260927'
READ = {}

def source(name):
    p = SRC / name
    READ[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
    return p

def read_json(name):
    return json.loads(source(name).read_text())

def read_tsv(name):
    with source(name).open(newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))

def q(value):
    a = Fraction(value)
    return str(a.numerator) if a.denominator == 1 else rf'\frac{{{a.numerator}}}{{{a.denominator}}}'

def mq(value):
    return '$' + q(value) + '$'

def lab(x):
    if x == '0': return '0'
    if x.startswith(('c','d')): return x[0] + '_{' + x[1:] + '}'
    return {'alpha':r'\alpha','alpha2':r'\alpha^2','rho':r'\rho',
            'alpha_rho':r'\alpha\rho','alpha2_rho':r'\alpha^2\rho'}.get(x,x)

def vec(xs):
    return '(' + ','.join(map(str, xs)) + ')'

def table(name, columns, header, rows, caption, label, size='small'):
    text = '\\begingroup\\'+size+'\n\\setlength{\\tabcolsep}{5pt}\n'
    text += '\\begin{longtable}{'+columns+'}\n'
    text += '\\caption{'+caption+'}\\label{expphysics:'+label+'}\\\\\n'
    h=' & '.join(header)+r'\\'
    text += '\\toprule\n'+h+'\n\\midrule\n\\endfirsthead\n'
    text += '\\multicolumn{'+str(len(header))+'}{l}{\\small\\itshape Continued from preceding page.}\\\\\n'
    text += '\\toprule\n'+h+'\n\\midrule\n\\endhead\n'
    text += '\\midrule\n\\multicolumn{'+str(len(header))+'}{r}{\\small\\itshape Continued on next page.}\\\\\n\\endfoot\n\\bottomrule\n\\endlastfoot\n'
    text += '\n'.join(' & '.join(map(str,row))+r'\\' for row in rows)
    text += '\n\\end{longtable}\n\\endgroup\n'
    (OUT/name).write_text(text)

def integer_phase(encoded):
    f = list(map(Fraction, json.loads(encoded)))
    den = math.lcm(*(x.denominator for x in f))
    ints = [int(x*den) for x in f]
    divisor = math.gcd(*ints)
    return tuple(x//divisor for x in ints)

def phase_tex(ints):
    terms=[]
    for n,unit in zip(ints,['',r'\sigma',r'\vartheta',r'\sigma\vartheta']):
        if not n: continue
        a=abs(n)
        term=(str(a) if a!=1 or not unit else '')+unit
        terms.append(('-' if n<0 else ('+' if terms else ''))+term)
    return ''.join(terms) or '0'

basis=read_json('full_weight_two/low_weight_basis.json')['fields']
summary=read_json('full_weight_two/complete_primary_couplings.json')
seed=read_json('full_weight_two/low_weight_couplings.json')
couplings=read_tsv('full_weight_two/complete_primary_couplings.tsv')
assert len(basis)==113 and len(couplings)==18365
highest={f['multiplet']:f for f in basis if f['lowering_powers']==[0,0]}

rows=[]
for m,f in highest.items():
    n,r=f['current_dimensions']
    rows.append([m,f['index'],f'$( {n},{r})$',mq(f['norm_squared'][0]),len(f['field'])])
table('highest_norms.tex','rrrrr',['$m$','first index','$(n_m,r_m)$','$N_{m,0,0}$','Fock terms'],rows,
      'All thirteen multiplet highest-vector norms in the saved lattice gauge. The last column counts stored nonzero Fock-basis terms; it is not a representation dimension.','highest-norms')

rows=[]
for f in basis:
    assert all(x=='0' for x in f['norm_squared'][1:])
    m=f['multiplet']; p,r=f['lowering_powers']; n,s=f['current_dimensions']
    factor=Fraction(f['norm_squared'][0])/Fraction(highest[m]['norm_squared'][0])
    assert factor == 8640**(2*p) * math.factorial(p)*math.factorial(n-1)//math.factorial(n-1-p) * math.factorial(r)*math.factorial(s-1)//math.factorial(s-1-r)
    rows.append([f['index'],f'$({m},{p},{r})$',f'$({f["Cartan_weight"][0]},{f["Cartan_weight"][1]})$',str(factor)])
table('basis_dictionary.tex','rrrr',['index $i$','$(m,p,q)$','$(H_L,H_R)$','$N_i/N_{m,0,0}$'],rows,
      'Complete index dictionary for all 113 weight-two Virasoro primaries. Multiplying the last column by Table~\\ref{expphysics:highest-norms} gives the actual squared norm.','basis-dictionary')

by_key={tuple(int(r[k]) for k in ['i','j','k']):r for r in couplings}
selected={tuple(e['indices']):e for e in summary['selected_examples']}
assert len(selected)==318
all_triples=Counter(tuple(basis[int(r[k])]['multiplet'] for k in ['i','j','k']) for r in couplings)
assert {tuple(e['multiplets']) for e in selected.values()}==set(all_triples)
rows=[]
for key,e in sorted(selected.items(),key=lambda item:(item[1]['multiplets'],item[0])):
    row=by_key[key]
    mag=json.loads(row['abs_C_squared_K4'])
    assert all(x=='0' for x in mag[1:])
    rows.append(['$'+vec(e['multiplets'])+'$','$'+vec(key)+'$',
                 '$'+phase_tex(integer_phase(row['numerator_K4']))+'$',mq(mag[0])])
table('reduced_coupling_atlas.tex','rrlr',[r'$(m,n,\ell)$','$(i,j,k)$',r'$\kappa$',r'$Q=|C_{ij}^{\ k}|^2$'],rows,
      r'Complete phase-sensitive representative atlas: one nonzero component for every nonzero ordered multiplet map. The coefficient is $C_{ij}^{\ k}=\kappa\sqrt{Q/(\overline\kappa\kappa)}$, with positive square roots. Use the index dictionary and the transvectant reconstruction in the text.','coupling-atlas')

rows=[]
for m in range(13):
    for n in range(13):
        targets=[ell for ell in range(13) if (m,n,ell) in all_triples]
        rows.append([m,n,('$'+','.join(map(str,targets))+'$') if targets else r'$\varnothing$',sum(all_triples[m,n,ell] for ell in targets)])
table('coupling_support.tex','rrlr',['first $m$','second $n$','nonzero target multiplets','nonzero components'],rows,
      'Exhaustive support of the primary tensor by ordered pair of multiplets. A missing target means the entire equivariant map vanishes; the final column counts all nonzero ordered component triples for that pair.','coupling-support')

rows=[]
for e in seed['stress_Ward_couplings']:
    rows.append([e['multiplet'],{'affine1':'$T_L$','affine39':'$T_R$','coset_e':'$T_e$','coset_f':'$T_f$'}[e['axis']],mq(e['central_charge']),mq(e['weight']),mq(e['normalized_C_squared'])])
table('stress_ward.tex','rlrrr',['$m$','stress','$c_i$','$h_i$','$2h_i^2/c_i$'],rows,
      'Resolved stress couplings for the eight original highest multiplets. These are intrinsic-stress projections, before changing to the total stress and the three orthogonal stress-difference primaries.','stress-ward')

cross=read_json('crosslink_checks.json')
rows=[]
for e in cross['u_pair_nonzero_targets']:
    f=basis[e['k']]
    rows.append([e['k'],'$'+vec([f['multiplet']]+f['lowering_powers'])+'$',mq(e['abs_C_squared'][0])])
table('u_pair_projections.tex','rrr',['target $k$','$(m,p,q)$',r'$|C_{68,95}^{\ k}|^2$'],rows,
      'All nine nonzero primary projections of the extremal $u$ pair. Their sum is $11/3$; targets 110, 111, 112 sum to $41/140$.','u-pair')

corr=read_json('correlators.json')
blocks=read_tsv('correlators.global_blocks.tsv')
groups=defaultdict(list)
for e in blocks: groups[e['correlator']].append(e)
titles={'u_neutral':'neutral weight-two generator','u_equal_charge':'equal-charge weight-two generator','Potts':'Potts spin-three generator','PF13':'level-thirteen parafermion spin-three generator','unit_Cartan':'unit Cartan current','unit_total_stress':'unit total stress tensor'}
for name,entries in groups.items():
    rows=[[e['global_weight'],mq(e['squared_coupling_sum']),mq(e['reduced_series_coefficient'])] for e in entries]
    table('blocks_'+name+'.tex','rrr',['$n$','$A_n$','$[x^n]x^{2h}G(x)$'],rows,
          'Global-block and reduced power-series coefficients through weight 32 for the '+titles.get(name,name).replace('_',' ') +'. All entries are copied as exact fractions.','blocks-'+name)

terms=corr['u_four_point']['terms']
rows=[]
for e in terms:
    if e['ordering'] not in ['mpmp','mmpp'] or not e['charge_conserving']: continue
    assert e['coefficient_before_charge_delta']==['1/9','0','0','0']
    rows.append([r'\texttt{'+e['ordering']+'}','$'+vec(e['vertex_choices'])+'$',e['cocycle_phase'],e['x_power'],e['one_minus_x_power']])
assert len(rows)==30
table('surviving_gaussian_terms.tex','lrrrr',['ordering','momentum choices','cocycle sign','$x$ exponent','$(1-x)$ exponent'],rows,
      'Every surviving Gaussian term in the two independent reflection-positive $u$ orderings. Choices are numbered 0,1,2 in the momentum order of the text; each complete normalized coefficient is $1/9$, including its adjoint and cocycle factors.','gaussian-terms')

rows=[]
for e in corr['lightest_chiral_blocks']['blocks']:
    rows.append([e['outer_triplet_index'],e['inner_triplet_index'],mq(e['one_minus_x_power']),mq(e['relative_weight1_coefficient']),mq(e['U_vacuum_current_part']),mq(e['X_equals_b_top_part'])])
table('lightest_blocks.tex','rrrrrr',['$i$','$j$','$(1-x)$ exponent','total weight 1','current part','$M_b$ part'],rows,
      'All nine selected lightest-module lattice blocks and their relative-weight-one decomposition. Each block also has the common factor $x^{-2/3}$.','lightest-blocks')

rows=[[r'\texttt{'+e['correlator'].replace('_',r'\_')+'}',mq(e['x']),mq(e['value'])] for e in corr['samples']]
table('correlator_samples.tex','lrr',['function','$x$','exact value'],rows,
      'All fifty saved rational-point evaluations. Ordering names use $p=\\widehat u$, $m=\\widehat u^\\dagger$ at $(\\infty,1,x,0)$; spin-three and Ward names refer to the unit fields.','correlator-samples')

defects=read_json('defect_data.json')
labels=defects['labels']; fusion=defects['fusion_N_ab_c']
rows=[]
for a in range(12):
    for b in range(a,12):
        rows.append(['$'+lab(labels[a])+'$','$'+lab(labels[b])+'$','$'+vec(fusion[a][b])+'$'])
table('fusion_complete.tex','rrl',['$a$','$b$','coefficient vector of $a\\otimes b$'],rows,
      'All 78 unordered center fusion products. Vectors are in the fixed order $(0,b,a,c_0,c_1,c_2,d_1,d_2,d_3,d_4,d_5,d_6)$; commutativity supplies the other 66 ordered products. Every entry of the 1728-entry tensor is therefore printed.','fusion-complete')

rows=[]
for e in read_tsv('Cardy_annuli.tsv'):
    if labels.index(e['boundary_a'])>labels.index(e['boundary_b']): continue
    rows.append(['$'+lab(e['boundary_a'])+'$','$'+lab(e['boundary_b'])+'$',mq(e['lowest_h']),e['identity_multiplicity'],mq(e['first_nonidentity_h_including_currents']),e['multiplicity']])
table('cardy_gaps.tex','rrrrrr',['$a$','$b$',r'$h_{\min}$','vacua','$h_{>0}$','multiplicity'],rows,
      'Ground states and first positive boundary weights for all 78 distinct Cardy annuli. The complete character coefficient vector is the corresponding row of Table~\\ref{expphysics:fusion-complete}. Reversing the boundaries gives the same row.','cardy-gaps')

text=[]
for e in defects['diagonal_U_twisted_sectors']:
    text.append(r'\subsubsection*{Line $'+lab(e['line'])+r'$}')
    text.append(r'\noindent Ground dimension $'+q(e['ground_dimension'])+r'$ with multiplicity '+str(e['ground_degeneracy'])+r'; first nonidentity scalar dimension $'+q(e['first_nonidentity_scalar_dimension'])+r'$ with multiplicity '+str(e['scalar_degeneracy'])+'.')
    text.append(r'\[\renewcommand{\arraystretch}{0.93}N_{'+lab(e['line'])+r'}=\left(\begin{array}{rrrrrrrrrrrr}')
    text.append('\\\\\n'.join('&'.join(map(str,row)) for row in e['character_bilinear_matrix']))
    text.append(r'\end{array}\right).\]')
(OUT/'twisted_matrices.tex').write_text('\n'.join(text)+'\n')

h3=defects['E8_H3']; hlabels=h3['labels']
rows=[]
for a in range(6):
    for b in range(6):
        rows.append(['$'+lab(hlabels[a])+'$','$'+lab(hlabels[b])+'$','$'+vec(h3['fusion_N_ab_c'][a][b])+'$'])
table('h3_fusion.tex','rrl',['$x$','$y$','coefficient vector of $x\\otimes y$'],rows,
      'All 36 ordered Haagerup products, in basis $(1,\\alpha,\\alpha^2,\\rho,\\alpha\\rho,\\alpha^2\\rho)$. Order matters.','h3-fusion')

rows=[]
for e in h3['U_preserving_boundary_annuli']:
    if hlabels.index(e['x'])>hlabels.index(e['y']): continue
    rows.append(['$'+lab(e['x'])+'$','$'+lab(e['y'])+'$','$'+vec(e['character_coefficients'])+'$',mq(e['first_nonidentity_h']),e['multiplicity']])
table('e8_annuli.tex','rrlrr',['$x$','$y$','$U$-character coefficient vector','$h_{>0}$','mult.'],rows,
      'All 21 distinct $U$-preserving annuli of the selected full $E_8$ theory. The vector order is the twelve-sector center order. Equal boundaries have one identity; distinct boundaries have none. Reversal gives the other 15 ordered annuli.','e8-annuli',size='footnotesize')

rows=[]
for e in read_tsv('E8_H3_twisted.tsv'):
    rows.append(['$'+lab(e['defect_x'])+'$',mq(e['lowest_Delta']),e['lowest_degeneracy'],mq(e['first_nonidentity_scalar_Delta']),e['scalar_degeneracy']])
table('h3_twisted_gaps.tex','rrrrr',['$x$',r'$\Delta_{\min}$','mult.',r'$\Delta_{\rm scalar}$','mult.'],rows,
      'All six first-factor Haagerup twisted Hilbert spaces, with the full antiholomorphic $E_8$ theory as spectator. Multiplicities here include the forgetful matrix.','h3-twisted-gaps')

rows=[]
for e in h3['tube_multiplicity_spaces']:
    rows.append(['$'+lab(e['label'])+'$',mq(e['lowest_Delta']),e['lowest_degeneracy'],mq(e['scalar_gap_excluding_identity']) if e['scalar_gap_excluding_identity'] is not None else r'none',e['scalar_gap_degeneracy']])
table('tube_spaces.tex','rrrrr',[r'$\mu$',r'$\Delta_{\min}$','mult.',r'$\Delta_{\rm scalar}$','mult.'],rows,
      'All twelve tube multiplicity spaces $\\mathcal V_\\mu=M_\\mu\\otimes\\overline{V_{E_8}}$. These rows exclude the finite-dimensional $W_x^\\mu$ factor. ``None'' means there is no scalar at any grade.','tube-spaces')

manifest={'purpose':'transcription and formatting of saved physics outputs, not a research replay',
          'coverage':{'basis_fields':len(basis),'nonzero_component_couplings':len(couplings),'nonzero_ordered_multiplet_maps':len(selected),'zero_ordered_multiplet_maps':13**3-len(selected),'global_block_families':list(groups),'global_block_rows':len(blocks),'center_unordered_fusion_products':78,'center_ordered_fusion_products':144,'h3_ordered_fusion_products':36,'distinct_cardy_annuli':78,'distinct_e8_annuli':21},
          'source_sha256':READ}
(OUT/'transcription_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
md='# Physics source inventory\n\nTables read existing outputs only. No research exporter was rerun.\n\n'
for name,digest in sorted(READ.items()): md+='- `'+name+'` — SHA-256 `'+digest+'`\n'
md+='\nCoverage is recorded in `physics_tables/transcription_manifest.json`. The original96-field tensor at the physics directory root is deliberately excluded in favor of `full_weight_two/`.\n'
(OUT.parent/'physics_sources.md').write_text(md)
print(json.dumps(manifest['coverage'],indent=2))
