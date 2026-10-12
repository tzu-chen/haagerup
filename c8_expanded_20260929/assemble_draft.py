#!/usr/bin/env python3
"""Assemble a separate verification draft; read existing results, never replay them."""
from pathlib import Path
import csv
import hashlib
import json
import re
import shutil
from collections import OrderedDict
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCES = {}


def read(path):
    p = ROOT / path
    b = p.read_bytes()
    SOURCES[path] = {"bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}
    return b.decode()


def data(path):
    return json.loads(read(path))


def tsv(path):
    return list(csv.DictReader(read(path).splitlines(), delimiter="\t"))


def esc(s):
    return str(s).replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("%", r"\%").replace("&", r"\&").replace("#", r"\#")


def rat(s):
    s = str(s)
    return s


def field_tex(vals):
    out = ""
    for val, sym in zip(vals, ["", "s", "t", "st"]):
        f = Fraction(val)
        if not f:
            continue
        sign = "-" if f < 0 else ("+" if out else "")
        a = abs(f)
        c = "" if a == 1 and sym else str(a)
        if "/" in c:
            n, d = c.split("/")
            c = r"\frac{" + n + "}{" + d + "}"
        out += sign + c + sym
    return out or "0"


def table(headers, rows, spec=None, size=r"\small"):
    spec = spec or ("r" * len(headers))
    h = " & ".join(headers) + r"\\"
    return ("\n\\begingroup" + size + "\n\\setlength{\\tabcolsep}{5pt}\n"
            + r"\begin{longtable}{@{}" + spec + "@{}}\n\\toprule\n" + h
            + "\n\\midrule\\endfirsthead\n\\toprule\n" + h
            + "\n\\midrule\\endhead\n\\bottomrule\\endfoot\n"
            + "\n".join(" & ".join(map(str, row)) + r"\\" for row in rows)
            + "\n\\end{longtable}\n\\endgroup\n")


def write(name, s):
    p = HERE / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s)


def flatten(path):
    text = read(path)
    target = HERE / "base" / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
    return re.sub(r"\\input\{([^}]+)\}", lambda m: flatten(m[1]), text)


def images(text):
    def repl(m):
        path = m[2]
        p = ROOT / path
        b = p.read_bytes()
        SOURCES[path] = {"bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}
        dest = HERE / "assets" / p.name
        shutil.copyfile(p, dest)
        return m[1] + "{assets/" + p.name + "}"
    text = re.sub(r"(\\includegraphics(?:\[[^]]*\])?)\{([^}]+)\}", repl, text)
    return re.sub(r"\\IfFileExists\{([^}]+/([^/}]+\.pdf))\}", lambda m: r"\IfFileExists{assets/" + m[2] + "}", text)


def assemble_base():
    original = read("hi_cft_c8_proof.tex")
    (HERE / "base/hi_cft_c8_proof.tex").write_text(original)
    bibliography = flatten("hi_cft_c8_bibliography.tex")
    text = original.replace(r"\input{hi_cft_c8_bibliography.tex}", "")
    text = re.sub(r"\\input\{([^}]+)\}", lambda m: flatten(m[1]), text)
    text = images(text)
    text = text.replace(r"\large Construction, spectrum and observables", r"\large Expanded verification draft\\[3pt]Construction, spectrum, observables and explicit data")
    text = text.replace(r"\date{27 September 2026}", r"\date{29 September 2026}")
    text = text.replace("pdfsubject={Physics and exact construction, with explicit review obligations}", "pdfsubject={Expanded verification draft assembled from the current manuscript and archived exact results}")
    text = text.replace("pdftitle={A central-charge-eight CFT with Haagerup symmetry: construction, spectrum and observables}", "pdftitle={Expanded verification draft: A central-charge-eight CFT with Haagerup symmetry}")
    text = text.replace(r"\fancyhead[R]{\small Review draft}", r"\fancyhead[R]{\small Expanded verification draft}")
    text = text.replace(r"\begin{document}", r"""\newcolumntype{P}[1]{>{\raggedright\arraybackslash}p{#1}}
\newcommand{\msref}[1]{\ref{#1}}
\newcommand{\mspageref}[1]{\pageref{#1}}
\newcommand{\msnameref}[1]{\nameref{#1}}
\makeatletter
\renewcommand*\@pnumwidth{2.5em}
\renewcommand*\@tocrmarg{3.5em}
\renewcommand*\l@section[2]{\@dottedtocline{1}{0em}{3em}{\bfseries #1}{\bfseries #2}}
\renewcommand*\l@subsection{\@dottedtocline{2}{1.5em}{3.7em}}
\renewcommand*\l@subsubsection{\@dottedtocline{3}{5.2em}{4.8em}}
\makeatother
\begin{document}""")
    text = text.replace(r"\clearpage" + "\n" + r"\tableofcontents", r"\input{reader_orientation.tex}" + "\n\\clearpage\n\\tableofcontents", 1)
    text = text.replace("\\section{Compilation and review scope}\\label{sec:compilation}\n", "\\section{Compilation and review scope of the base revision}\\label{sec:compilation}\nThe following source names describe the preserved 27 September revision. This expanded draft has separate build instructions in Appendix~\\ref{exp:assembly}.\n")
    tail = r"""
\clearpage
\renewcommand{\thesection}{S\arabic{section}}
\renewcommand{\theHsection}{supplement.\arabic{section}}
\setcounter{section}{0}
\part{Integrated human verification guide}
\input{verification_guide.tex}
\clearpage
\part{Additional finite construction records}
\begingroup
\setlength{\extrarowheight}{1.5pt}
\input{finite_details.tex}
\clearpage
\part{Additional structure and analytic records}
\input{structure_details.tex}
\clearpage
\part{Interaction, defect and boundary data}
\input{physics_details.tex}
\clearpage
\part{Complete spectral and coordinate tables}
\input{spectral_details.tex}
\input{coordinate_details.tex}
\input{top_details.tex}
\endgroup
\clearpage
\part{Formalization scope and source concordance}
\input{lean_scope.tex}
\input{source_concordance.tex}
\clearpage
\addcontentsline{toc}{section}{References}
\input{bibliography.tex}
\end{document}
"""
    text = text.replace(r"\end{document}", tail)
    write("haagerup_c8_expanded.tex", text)
    write("bibliography.tex", bibliography)

    guide = flatten("hi_cft_c8_verification_guide.tex")
    guide = guide[guide.index(r"\section{How to audit the inputs}"):guide.index(r"\end{document}")]
    start = guide.index("The reference manuscript is")
    end = guide.index("This companion makes", start)
    guide = guide[:start] + "The following guide is incorporated from the 27 September companion. All manuscript references now resolve within this volume. Original artifact paths identify the archived sources. " + guide[end:]
    guide = guide.replace(r"\href{hi_cft_c8_proof.pdf}{manuscript}", "base manuscript")
    guide = guide.replace("All $337$ monomials", "All $337$ monomials (also printed in Appendix~\\ref{expdata:coordinates})")
    guide = guide.replace(r"The companion\n\artifact{hi_cft_c8_lean_assessment.pdf}", "The integrated formalization assessment")
    guide = guide.replace("The companion\n\\artifact{hi_cft_c8_lean_assessment.pdf}", "The integrated formalization assessment in Appendix~\\ref{sec:review-lean}")
    guide = guide.replace(r"keys \texttt{potts\_stress}, \texttt{weight\_three\_primary};", r"keys \path{potts_stress}, \path{weight_three_primary};")
    write("verification_guide.tex", guide)
    lean = flatten("c8_physics_20260927/lean_baseline_assessment.tex") + "\n" + flatten("c8_physics_20260927/lean_assessment.tex")
    lean = lean.replace(r"P{0.09\linewidth}P{0.59\linewidth}P{0.24\linewidth}", r"P{0.11\linewidth}P{0.57\linewidth}P{0.24\linewidth}")
    write("lean_scope.tex", lean)


def spectral_tables():
    chars = data("c8_physics_20260927/data/characters.json")
    fm = data("c8_physics_20260927/data/fundamental_matrix.json")
    s = r"""\section{Character and recurrence tables through grade twenty-four}
\label{expdata:characters}
These tables transcribe the completed 27 September release. They add no
new character-identification assumption. Every coefficient is an exact
integer, and every grade is measured from the actual lowest weight $h_i$.
The column $v_i(n)$ includes the vacuum identity once. The formulas in
Section~\ref{sec:physics-spectrum} reconstruct every displayed full-spectrum
entry from these chiral tables. Equal $a$ and $c_0$ characters still label
two different modules.

The source is \artifact{c8_physics_20260927/data/characters.json}.
All thirteen rows of modules below (twelve $U$ modules and the $E_8$
vacuum module) retain all twenty-five supplied grades.
"""
    for m in chars["modules"] + [chars["holomorphic_E8"]]:
        name = m["module"]
        s += "\n\\subsection{Module " + esc(name) + "}\n"
        s += "$h=" + m["h"] + r"$; $\chi=q^{h-1/3}\sum_n a(n)q^n$." + "\n"
        rows = [(n, a, v) for n, (a, v) in enumerate(zip(m["state_multiplicities"], m["virasoro_primary_multiplicities_including_identity"]))]
        s += table(["Grade $n$", "States $a(n)$", "Virasoro primaries $v(n)$"], rows)
    s += r"""\subsection{All entries of the characteristic matrix}
\label{expdata:recurrence}
Source: \artifact{c8_physics_20260927/data/fundamental_matrix.json}.
The row and column order is $(0,b,a,c_0,c_1,c_2,d_1,d_2,d_3,d_4,d_5,d_6)$.
The exponent diagonal is
\[
\Lambda=\operatorname{diag}(""" + ",".join(fm["Lambda"]) + r""" ).
\]
To keep each integer legible, the twelve-by-twelve characteristic matrix
$\chi=X_0$ is printed in two six-column panels. The panels have the same
row ordering and must be concatenated horizontally, not vertically.
"""
    for lo in [0, 6]:
        s += table(["$i$ "] + [f"$j={j}$" for j in range(lo,lo+6)], [[i]+row[lo:lo+6] for i,row in enumerate(fm["chi"])], size=r"\footnotesize")
    s += r"""\subsection{Scalar modular-form recurrence coefficients}
These are the complete saved $f_r,g_r$ used in the matrix recurrence.
The values at $r=25$ are needed by the nonvacuum grade-twenty-four
calculation. The recurrence in equation~\ref{eq:physics-xi-recurrence},
$X_{-1}=I$, and the matrix above are a compact exact specification of all
saved $12\times12$ coefficient matrices. Printing their 3,744 individual
entries would duplicate this finite specification without changing its
scope.
"""
    s += "The two scalar sequences are printed separately to preserve legibility of the largest integers.\n"
    for key in ['f','g']:
        s += table(["$r$", "$"+key+"_r$"], [[i,x] for i,x in enumerate(fm[key])], size=r"\scriptsize")
    s += r"""\section{Full scalar spectrum through total dimension twenty-four}
\label{expdata:scalars}
Source: \artifact{c8_physics_20260927/data/scalars.tsv}.
These are all recorded scalar levels, not only relevant or marginal
ones. ``States'' includes descendants; ``primaries'' removes both
left and right Virasoro descendants. The identity occurs at zero.
The counts describe undeformed theories and do not assert exact
marginality for dimension-two perturbations.
"""
    rows = tsv("c8_physics_20260927/data/scalars.tsv")
    for theory in OrderedDict.fromkeys(r['theory'] for r in rows):
        s += "\\subsection{" + esc(theory) + "}\n"
        s += table([r"$\Delta$", "States", "Primary components"], [[r['Delta'],r['states'],r['Virasoro_primaries']] for r in rows if r['theory']==theory])
    s += r"""\section{Complete spin-resolved spectrum through dimension twenty-four}
\label{expdata:spins}
The next tables preserve every saved $(\Delta,|s|)$ value. For $s>0$,
each printed multiplicity is the multiplicity at spin $+s$ separately
and also at spin $-s$ separately: it is not their sum. The two opposite
spin rows in each original TSV agree entry by entry. A spin-zero row
appears once. Thus no spectral information is lost by this folding.
The state and primary columns have the same meaning as in
Appendix~\ref{expdata:scalars}. Rows with zero primary multiplicity are
retained when they contain descendant states.
"""
    for name, path in [("Diagonal U", "diagonal_spectrum.tsv"), ("Holomorphic E8 full theory", "e8_spectrum.tsv")]:
        full = "c8_physics_20260927/data/" + path
        rows = tsv(full)
        by = {(r['Delta'],int(r['spin'])):r for r in rows}
        for r in rows:
            q=by[(r['Delta'],-int(r['spin']))]
            assert (r['states'],r['Virasoro_primaries'])==(q['states'],q['Virasoro_primaries'])
        folded=[r for r in rows if int(r['spin'])>=0]
        s += "\\subsection{" + name + "}\nSource: \\artifact{" + full + "}. " + str(len(rows)) + " signed-spin rows are represented by " + str(len(folded)) + " nonnegative-spin rows.\n"
        s += table([r"$\Delta$", "$|s|$", "States at each spin", "Primaries at each spin"], [[r['Delta'],r['spin'],r['states'],r['Virasoro_primaries']] for r in folded], size=r"\footnotesize")
    s += thermal_tables()
    write("spectral_details.tex", s)


def interval(x, decimals=12):
    with localcontext() as c:
        c.prec=120
        q=Decimal(1).scaleb(-decimals)
        lo=Decimal(x['lower']).quantize(q,rounding=ROUND_FLOOR)
        hi=Decimal(x['upper']).quantize(q,rounding=ROUND_CEILING)
        assert lo<=Decimal(x['lower'])<=Decimal(x['upper'])<=hi
        return "["+format(lo,'f')+",\\,"+format(hi,'f')+"]"


def thermal_tables():
    d=data("c8_physics_20260927/data/thermal.json")
    s=r"""\section{Certified thermal intervals and explicit tail certificates}
\label{expdata:thermal}
The source \artifact{c8_physics_20260927/data/thermal.json} stores
eighty-digit directed-rounding intervals. Here every endpoint is rounded
\emph{outward} to twelve digits after the decimal point, so the printed
interval still encloses the stored interval. These wider intervals are
conditional on positivity and full modular invariance, as explained in
Section~\ref{sec:physics-spectrum}. The table is a transcription and
outward rounding of saved output, not a fresh thermal calculation.

Set $t=\beta v/L$, $b=2\pi t$, and $E=\Delta-2/3$.
The six columns printed as individual rows are $Z$, $\log Z$,
$F/(2\pi v/L)=-\log Z/b$, $\langle E\rangle$,
$C_V=b^2\operatorname{Var}(E)$, and $S=\log Z+b\langle E\rangle$.
The energy zero at $t=1$ is exact under the modular premise.
"""
    names=[('Z','$Z$'),('log_Z',r'$\log Z$'),('free_energy_in_units_2pi_v_over_L',r'$F/(2\pi v/L)$'),('mean_Delta_minus_2_over_3',r'$\langle E\rangle$'),('heat_capacity','$C_V$'),('entropy','$S$')]
    for theory, rows in d['theories'].items():
        s+='\\subsection{'+esc(theory)+'}\n'
        tr=[]
        for r in rows:
            for k,label in names:
                tr.append(['$'+r['t_beta_v_over_L']+'$',label,'$'+interval(r[k])+'$'])
        s+=table(['$t$','Observable','Enclosing interval'],tr,spec='cll',size=r'\footnotesize')
        s+=r"""The following positive bounds are rounded upward to eight significant
digits. $H$ bounds the partition-function tail at the modular evaluation
temperature. $M_1,M_2$ bound omitted energy moments at the requested
temperature; these use the separate moment-tail certificate and its
reference temperature $t_0$. The exact cutoff is $D=24$, hence
$E_D=70/3$.
"""
        def upper(v):
            with localcontext() as c:
                c.prec=8;c.rounding=ROUND_CEILING
                v=+Decimal(v)
                a,e=format(v,'.7E').split('E')
                return '$'+a+r'\times10^{'+str(int(e))+'}$'
        tr=[]
        for r in rows:
            m=r['modular_tail_certificate'];mom=r['moment_tail_certificate']
            tr.append([r['t_beta_v_over_L'],m['evaluated_t'],upper(m['tail_upper_at_evaluated_t']),mom.get('t0','--'),upper(mom['first_moment_tail_upper']),upper(mom['second_moment_tail_upper'])])
        s+=table(['$t$',r'$t_{\rm eval}$','$H$ upper bound','$t_0$','$M_1$ upper bound','$M_2$ upper bound'],tr,size=r'\scriptsize')
    return s


def coordinates():
    s=r"""\section{Complete coordinate atlas for the small verification fields}
\label{expdata:coordinates}
All 337 rows of \artifact{c8_reviewability_20260927/grade2_fields.tsv}
are printed below, followed by the additional 434 rows for the two
weight-three structural fields in
\artifact{c8_reviewability_20260927/structural_fields.tsv}. The latter
also repeats the 91 rows of $p,z$; those repetitions agree exactly with
the first table and are printed only once. No coefficient is rounded.

Use $s=\sqrt{13}>0$, $t=i\sqrt3$, in the ordered coefficient basis
$(1,s,t,st)$. In a row $(\lambda;\mathcal O;c)$, the contribution is
$c\prod_{j\in\mathcal O}\alpha_{j\bmod8}(-1-\lfloor j/8\rfloor)e^\lambda$.
The momentum is always an eight-tuple in the ordered simple-root basis.
An empty oscillator list is denoted $\varnothing$. Oscillators commute;
the lists have no factorial or divided-power normalization. Each field
is the sum of every row in its subsection. Unlisted states have zero
coefficient. These are actual saved vectors, not new membership proofs.
The exact products and membership equations belong to the integrated
verification guide and the finite construction appendices.
"""
    a=tsv('c8_reviewability_20260927/grade2_fields.tsv')
    b=tsv('c8_reviewability_20260927/structural_fields.tsv')
    common=set(r['field'] for r in a)&set(r['field'] for r in b)
    for f in common:
        assert [r for r in a if r['field']==f]==[r for r in b if r['field']==f]
    rows=a+[r for r in b if r['field'] not in common]
    name={'omega':r'\omega_B','omegaL':r'\omega_L','omegaR':r'\omega_R','w':r'w_{\rm PF13}','w_P':r'w_{\rm Potts}'}
    for f in OrderedDict.fromkeys(r['field'] for r in rows):
        rr=[r for r in rows if r['field']==f]
        s+='\n\\subsection{Field '+esc(f)+'}\n'
        s+='$'+name.get(f,f)+'$: '+str(len(rr))+' nonzero monomials.\n'
        if f=='w':
            s+=r'''The export name \texttt{w} denotes the \emph{unnormalized}
parafermion weight-three field $w$. The normalized reconstruction
generator is $a=\sigma w$, where
\[
\sigma^2=-\frac{7+3st}{9223500},\qquad
w_5w=(-86086+36894st)\one,\qquad a_5a=\frac8{15}\one.
\]
The coefficients below are those of $w$, without the factor $\sigma$.
It is also distinct from the Potts generator \texttt{w\_P}.
The complex number in $w_5w$ is a bilinear self-OPE coefficient;
it is not the positive Hermitian squared norm of the raw vector.
'''
        if f=='w_P':
            s+=r'''This is the raw Potts weight-three field. Its bilinear
self-OPE coefficient is $(w_P)_5w_P=8424\one$. The canonical field
used in the spin-three OPE formulas and its unit version are
\[
a_{\rm Potts}=\frac{w_P}{\sqrt{31590}},\qquad
(a_{\rm Potts})_5a_{\rm Potts}=\frac4{15}\one,\qquad
\widehat a_{\rm Potts}=\frac{w_P}{\sqrt{8424}},
\]
with the common overall sign chosen consistently. The rows below retain
the raw coefficients and have not been divided by either square root.
'''
        tr=[]
        for r in rr:
            tr.append(['$('+r['momentum']+')$','$'+('('+r['oscillators']+')' if r['oscillators'] else r'\varnothing')+'$','$'+field_tex([r[k] for k in ['q0','qs','qt','qst']])+'$'])
        s+=table([r'Momentum $\lambda$',r'Oscillators $\mathcal O$','Exact coefficient'],tr,spec='lll',size=r'\scriptsize')
    write('coordinate_details.tex',s)


if __name__ == '__main__':
    assemble_base()
    spectral_tables()
    coordinates()
    write('assembly_inputs.json',json.dumps({'scope':'Input identity for document assembly; no research replay is claimed.','files':SOURCES},indent=2)+'\n')
    print('Assembled draft, integrated guides, spectral tables and coordinate atlas.')
    print('Source files read:',len(SOURCES))
