#!/usr/bin/env python3
"""Typeset saved top witnesses. No matrix products or research replays."""
from pathlib import Path
from collections import OrderedDict
from fractions import Fraction
import hashlib,json,csv
from assemble_draft import field_tex,table

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
INPUTS={}

def read(path):
    p=ROOT/path;b=p.read_bytes()
    INPUTS[path]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
    return b.decode()

def ftex(x):
    # Break long algebraic coefficients at their plus signs in table cells.
    return field_tex(x).replace('+',r'+\allowbreak ')

def recipe_tex(i,r,seedkey):
    inp=r['input']
    if seedkey in inp:
        return '$r_{'+str(i)+'}=e_{'+str(inp[seedkey])+'}$'
    src='M_{'+str(inp['operator'])+'}r_{'+str(inp['parent'])+'}'
    red=''.join(r'-\allowbreak \bigl('+ftex(c)+r'\bigr)r_{'+str(j)+'}' for j,c in r['reductions'])
    scale=ftex(r['scale'])
    return '$r_{'+str(i)+r'}=\bigl('+scale+r'\bigr)\bigl['+src+red+r'\bigr]$'

def build():
    s=r'''\section{Complete finite top witness atlas}
\label{expdata:top-atlas}
This appendix fills in the finite coordinate and cyclic-generation
records that the integrated guide illustrates with its first few rows.
The tables are literal saved witnesses. Checking each row's mode action
and elimination, together with distinct pivots, is the finite cyclicity
argument. Merely counting the rows is not that verification. The ambient
VOA interpretation, positive metric, invariant subspace, and all-weight
module conclusion retain the separate hypotheses explained in
Appendix~\ref{hr:structural-inputs}.

\subsection{All six joint spectral eigenvectors}
The source is
\artifact{c8_reviewability_20260927/core_spectral_witnesses.tsv}.
Each of the six vectors has 21 nonzero terms, and has parafermion weight
$12/13$. The current charges distinguish the blocks. Coefficients use
$s=\sqrt{13}$, $t=i\sqrt3$ as in the coordinate atlas; oscillator indices
have the same meaning. Each subsection below specifies one entire vector
as the sum of its displayed monomials.
'''
    rows=list(csv.DictReader(read('c8_reviewability_20260927/core_spectral_witnesses.tsv').splitlines(),delimiter='\t'))
    for charge in OrderedDict.fromkeys(r['Cartan_weight'] for r in rows):
        rr=[r for r in rows if r['Cartan_weight']==charge]
        s+=r'\paragraph{Cartan weight $('+charge+')$.}\n'
        s+=table([r'Momentum $\lambda$',r'Oscillators $\mathcal O$','Coefficient'],[
            ['$('+r['momentum']+')$','$'+('('+r['oscillators']+')' if r['oscillators'] else r'\varnothing')+'$','$'+ftex([r[k] for k in ['q0','qs','qt','qst']])+'$'] for r in rr],spec='lll',size=r'\scriptsize')
    d=json.loads(read('c8_reviewability_20260927/current80_witness.json'))
    s+=r'''\subsection{The 86-state ambient basis and the eighty-current complement}
\label{expdata:80-top}
Source: \artifact{c8_reviewability_20260927/current80_witness.json}.
The 86 ambient basis states are ordered as follows. Oscillator rows are
Cartan states; the remaining rows are root exponentials. The positive
Hermitian form is the lattice Gram form on the Cartan states and the
transported torus norm on the mutually orthogonal root states, as specified
in the integrated guide. These ambient basis indices are the $e_j$ used
in the subsequent complement and cyclic-row tables.
'''
    s+=table(['$j$',r'Momentum $\lambda$',r'Oscillators $\mathcal O$'],[
        [i,'$('+','.join(map(str,r['momentum']))+')$','$'+('('+','.join(map(str,r['oscillators']))+')' if r['oscillators'] else r'\varnothing')+'$'] for i,r in enumerate(d['ambient_states'])],spec='rll',size=r'\scriptsize')
    s+=r'''Every supplied complement row is printed next. This is an
80-row basis of $K_{\rm cur}^{\perp}\cap B_1$, not a second choice of
ambient coordinates. The symbol $b_i$ is used here only for these rows;
it is unrelated to the module label $b$. The recorded independent matrix
check verifies orthogonality to the current plane, positive metric, and
independence.
'''
    cr=[]
    for i,row in enumerate(d['complement_rows']):
        expr=r'+\allowbreak '.join(r'\bigl('+ftex(c)+r'\bigr)e_{'+str(j)+'}' for j,c in row)
        cr.append([i,'$b_{'+str(i)+'}='+expr+'$'])
    s+=table(['$i$','Complete complement row'],cr,spec=r'rP{.82\linewidth}',size=r'\footnotesize')
    s+=r'''\subsection{Operator indices and all eighty cyclic recipes}
The original current names $K0,\ldots,K5$ denote
$(H_L,E_L,F_L,H_R,E_R,F_R)$ in that order. The weight-two field
names $\mathrm{field}0,\ldots,\mathrm{field}7$ denote the charged
highest fields $a_0,\ldots,a_7$ in the finite supplement, and
$\mathrm{field}8$ is the retained neutral stress $e$. Each even
operator index is followed by its adjoint. The current operators use
mode zero; the weight-two operators use mode one. The adjoints are with
respect to the transported positive form, so replacing an adjoint by an
unscaled Chevalley lowering operator can change a row.
'''
    s+=table(['$j$','Saved operator name'],[[i,r'\texttt{'+o['name']+'}'] for i,o in enumerate(d['operators'])],spec='rl')
    s+=r'''The symbols $b_i$ and $r_i$ in this appendix are local names for
the complement and cyclic rows. They are not the $b_i$ membership basis
or the $r_i$ short-generation basis in the finite supplement.
In the next table, $r_i$ is normalized after subtracting the
earlier rows, exactly in the order written. The pivot is an ambient basis
index. The unique seed has Cartan weight $(0,10)$ and ambient index 76.
All referenced parents and reduction rows precede the new row. A list of
recipes still requires the claimed identification of the matrices with
field modes; those finite-mode obligations are separate from reading
the scalar coefficients.
'''
    s+=table(['$i$','Pivot','Exact cyclic-row recipe'],[[i,r['pivot'],recipe_tex(i,r,'seed_basis_index')] for i,r in enumerate(d['recipes'])],spec=r'rrP{.80\linewidth}',size=r'\footnotesize\setlength{\lineskip}{2pt}\setlength{\lineskiplimit}{2pt}')
    tops=json.loads(read('hi_cft_20260923_next_81top_all.json'))
    s+=r'''\subsection{All four mixed 81-dimensional tops: basis and recipes}
\label{expdata:81-tops}
Source: \artifact{hi_cft_20260923_next_81top_all.json}; its readable
recipe export is \artifact{c8_reviewability_20260927/top81_pivots.tsv}.
Each root basis is printed as the integer tuple $3\beta_j$. Thus the
actual momentum is one third of that tuple, not the tuple itself.
The listed norm is the exact diagonal Hermitian entry
$\langle e^{\beta_j},e^{\beta_j}\rangle$. Every table is specific to its
glue and sector signs; no unproved identification of the four bases is
used to discard repeated-looking rows. All four seeds have index 68 and
Cartan weight $(0,10)$.

The operator index order is the same interleaved field/adjoint order
listed above, now acting in the indicated mixed lattice sector. Each
sector uses its actual overlattice cocycle and quadratic gauge. The
mode-on-root rules in the integrated guide specify the elementary
calculation, while the archived matrix metadata binds the sector-specific
action. The full sparse elimination rows and matrix hashes remain in
the source; this appendix prints the complete basis, metric, pivot
schedule, and all recipes needed to reconstruct those rows.
'''
    for sector in tops['sectors']:
        assert [o['name'] for o in sector['operator_matrices']]==[o['name'] for o in d['operators']]
        label=f"({sector['glue_sign']},{sector['sector_sign']})"
        s+=r'\subsubsection{Glue and sector signs '+label+'}\n'
        br=[]
        for i,(root,norm) in enumerate(zip(sector['roots'],sector['metric'])):
            vals=[3*Fraction(x) for x in root]
            assert all(x.denominator==1 for x in vals)
            br.append([i,'$('+','.join(str(x) for x in vals)+')$','$'+norm+'$'])
        s+=table(['$j$',r'$3\beta_j$','Squared norm'],br,spec='rll',size=r'\scriptsize')
        rr=[]
        for i,(row,r) in enumerate(zip(sector['rows'],sector['recipes'])):
            rr.append([i,row[0][0],'$('+','.join(map(str,r['weight']))+')$',recipe_tex(i,r,'seed_index')])
        s+=table(['$i$','Pivot','Cartan weight','Exact cyclic-row recipe'],rr,spec=r'rrlP{.64\linewidth}',size=r'\footnotesize\setlength{\lineskip}{2pt}\setlength{\lineskiplimit}{2pt}')
    assert all(ord(c)>=32 or c in '\n\t' for c in s), 'Unexpected control character in TeX output'
    (HERE/'top_details.tex').write_text(s)
    (HERE/'top_transcription_inputs.json').write_text(json.dumps({'scope':'Saved finite witness transcription; no mode or matrix replay.','files':INPUTS},indent=2)+'\n')
    print('Wrote six spectral eigenvectors, eighty-current basis and recipes, four complete top bases and recipes.')

if __name__=='__main__':build()
