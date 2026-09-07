#!/usr/bin/env python3
"""Convert the Haagerup-Izumi handoff notes (Markdown + LaTeX math) into a
self-contained amsart paper.  Read-only with respect to its input.

Usage:
    python3 md2tex.py haagerup_izumi_class_field_stark_notes.md \
                      haagerup_izumi_notes.tex
    pdflatex haagerup_izumi_notes.tex   # three times, for the ToC and links

NOTE: THEOREMS below pins the proposition/proof blocks by line number in the
Markdown source.  Editing the source shifts those; the assertion in the setup
loop then fails loudly, and the numbers need updating rather than the output
being silently wrong.
"""
import re, sys

SRC, OUT = sys.argv[1], sys.argv[2]
lines = open(SRC, encoding='utf-8').read().split('\n')

# ---------------------------------------------------------------- theorems --
# Bold lead-ins such as "**Theorem.**", "**Rigidity theorem.**",
# "**Theorem (exact computation).**" or "**Proof of the residual identity.**"
# become amsthm environments.  A statement runs to the next blank line; a
# proof runs to its QED mark.  A lead-in that is not a recognized statement
# kind ("**Prior work.**", "**Remaining equation.**", ...) stays an ordinary
# bold run-in, and so does any block whose extent cannot be resolved: the
# converter degrades to plain text and warns rather than failing.
QED     = '∎'
QEDMARK = '\x13'          # survives escaping; expanded in the finished document
LEAD    = re.compile(r'^\*\*(.+?)\.\*\*(?=\s|$)')
KINDS   = {'theorem': 'theorem', 'proposition': 'proposition', 'lemma': 'lemma',
           'corollary': 'corollary', 'conjecture': 'conjecture',
           'criterion': 'proposition'}

def classify(label):
    """Bold label -> (amsthm environment, optional name) or (None, None)."""
    m = re.search(r'\s*\(([^)]*)\)\s*$', label)
    paren = m.group(1) if m else None
    base = (label[:m.start()] if m else label).strip()
    low = base.lower()
    if low.startswith('proof'):
        return 'proof', (label.strip() if low != 'proof' else None)
    last = re.split(r'[\s,:]+', low)[-1]
    env = KINDS.get(last)
    if env is None:
        return None, None
    if paren:
        return env, paren
    if last == env:
        return env, (' '.join(base.split()[:-1]) or None)
    return env, base            # e.g. "Sign descent criterion" -> proposition

def find_theorems(lines):
    marks = []
    for i, l in enumerate(lines):
        m = LEAD.match(l)
        if m:
            env, note = classify(m.group(1))
            marks.append((i, m.end(), env, note))
    stops = sorted([i for i, _, env, _ in marks if env]
                   + [i for i, l in enumerate(lines) if l.startswith('#')])
    blocks = []
    for i, cut, env, note in marks:
        if env is None:
            continue
        nxt = next((t for t in stops if t > i), len(lines))
        if env == 'proof':
            j = next((k for k in range(i, nxt) if QED in lines[k]), None)
            if j is None:
                sys.stderr.write('note: proof at line %d has no QED mark before '
                                 'the next block; left as bold text\n' % (i + 1))
                continue
        else:
            j = i
            while j + 1 < nxt and lines[j + 1].strip():
                j += 1
            if j + 1 < nxt:
                pass                      # ended on a blank line, as expected
            elif j + 1 < len(lines) and lines[j + 1].strip():
                sys.stderr.write('note: %s at line %d runs into the next block; '
                                 'left as bold text\n' % (env, i + 1))
                continue
        blocks.append((i, j, cut, env, note))
    return blocks

BEG, END = '\x10BEG\x10', '\x10END\x10'
_blocks = find_theorems(lines)
for i, j, cut, env, note in sorted(_blocks, reverse=True):
    lines[i] = lines[i][cut:].lstrip()
    lines[j] = re.sub(r'\s*' + QED + r'\s*$', '', lines[j])
    lines.insert(j + 1, END + '\\end{%s}' % env)
    lines.insert(i, BEG + '\\begin{%s}%s'
                 % (env, '[%s]' % note if note else ''))
# a QED mark outside any detected proof keeps a visible end-of-argument symbol
lines = [re.sub(r'\s*' + QED + r'\s*$', QEDMARK, l) for l in lines]

# ------------------------------------------------------------ inline layer --
CODE, LINK = [], []
C0, C1, L0, L1, M0, M1 = '\x02', '\x03', '\x04', '\x05', '\x06', '\x07'
SECTION_LABELS = set()

def esc_tt(s):
    s = s.replace('\\', '\\textbackslash{}')
    for ch in '&%$#_{}':
        s = s.replace(ch, '\\' + ch)
    s = s.replace('~', '\\textasciitilde{}').replace('^', '\\textasciicircum{}')
    return s.replace('\\_', '\\_\\allowbreak ')   # long file names may wrap

def esc_url(s):
    for ch in '%#&':
        s = s.replace(ch, '\\' + ch)
    return s

UNI = [('\u2013', '--'), ('\u2014', '---'), ('\u201c', '``'), ('\u201d', "''"),
       ('\u00f6', '\\"o'), ('\u00e9', "\\'e"), ('\u220e', '')]

def esc_text(s):
    s = s.replace('\\', '\x11')
    for ch in '&%$#_{}':
        s = s.replace(ch, '\\' + ch)
    s = s.replace('~', '\\textasciitilde{}').replace('^', '\\textasciicircum{}')
    if '\x11' in s:
        sys.stderr.write('warning: stray backslash in text: %r\n' % s)
    s = s.replace('\x11', '\\textbackslash{}')
    for a, b in UNI:
        s = s.replace(a, b)
    return s

def emphasis(s):
    s = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', s, flags=re.S)
    return re.sub(r'(?<!\*)\*(?!\s)(.+?)(?<!\s)\*(?!\*)', r'\\emph{\1}', s, flags=re.S)

NUM = r'\d+(?:\.\d+)?'
XREF = re.compile(r'\b(Sections?)((?:\s+' + NUM + r')(?:\s*(?:,|and|--|to)\s*' + NUM + r')*)')

def link_sections(s):
    def one(m):
        def sub(mm):
            n = mm.group(0)
            return '\\hyperref[sec:%s]{%s}' % (n, n) if n in SECTION_LABELS else n
        return m.group(1) + re.sub(NUM, sub, m.group(2))
    return XREF.sub(one, s)

def inline(text, xref=True):
    math = []
    text = re.sub(r'\\\(.*?\\\)',
                  lambda m: (math.append(m.group(0)) or M0 + str(len(math) - 1) + M1),
                  text, flags=re.S)
    text = re.sub(r'`([^`]*)`',
                  lambda m: (CODE.append(m.group(1)) or C0 + str(len(CODE) - 1) + C1), text)
    text = re.sub(r'\[([^\]]*)\]\(([^)\s]+)\)',
                  lambda m: (LINK.append((m.group(1), m.group(2))) or L0 + str(len(LINK) - 1) + L1),
                  text)
    text = emphasis(esc_text(text))
    if xref:
        text = link_sections(text)

    def put_link(m):
        label, url = LINK[int(m.group(1))]
        body = inline(label, xref=False)
        if url.startswith(('http://', 'https://', 'mailto:')):
            return '\\href{%s}{%s}' % (esc_url(url), body)
        return body                       # local file: keep the name, drop the link
    text = re.sub(L0 + r'(\d+)' + L1, put_link, text)
    text = re.sub(C0 + r'(\d+)' + C1,
                  lambda m: '\\texttt{%s}' % esc_tt(CODE[int(m.group(1))]), text)
    return re.sub(M0 + r'(\d+)' + M1, lambda m: math[int(m.group(1))], text)

def pdfstring(title_md):
    s = re.sub(r'\\\((.*?)\\\)', r'\1', title_md, flags=re.S)
    s = re.sub(r'`([^`]*)`', r'\1', s)
    s = re.sub(r'\*\*?(.+?)\*\*?', r'\1', s)
    s = re.sub(r'\\operatorname|\\mathbb|\\mathfrak|\\mathcal|\\mathrm|\\', ' ', s)
    for ch in '{}$_^':
        s = s.replace(ch, '')
    s = s.replace('\u2013', '-').replace('\u2014', '--')
    return re.sub(r'\s+', ' ', s).strip()

# ------------------------------------------------------------- block layer --
HEAD  = re.compile(r'^(#{1,6})\s+(.*?)\s*$')
FENCE = re.compile(r'^\s*```(\w*)\s*$')
HRULE = re.compile(r'^\s*(-{3,}|\*{3,}|_{3,})\s*$')
ITEM  = re.compile(r'^(\s*)([-*+]|\d+[.)])\s+(.*)$')
TSEP  = re.compile(r'^\s*\|[\s:|-]+\|\s*$')

# One boxed sentence is too wide for the measure; set it on two lines.
WIDE_BOX_OLD = ('\\text{Cyclic Haagerup--Izumi Q-system \\(F\\)-symbols are '
                'class-field-theoretic objects over }\nK_p=\\mathbb Q(\\sqrt{p^2+4}).')
# Presentation-only reflows: two displays whose source lines overrun the
# measure.  Each pair rewrites the maths alone, leaving any \tag outside.
DISPLAY_REFLOWS = [
    (r""" q_1\big|_{n=7}=10.3078696780804590050094397024\ldots,\qquad
 q_2\big|_{n=7}=5.4484617205726756972518020268\ldots.""",
     r""" \begin{gathered}
 q_1\big|_{n=7}=10.3078696780804590050094397024\ldots,\\
 q_2\big|_{n=7}=5.4484617205726756972518020268\ldots.
 \end{gathered}"""),
    (r""" R_a=\delta/u_a\quad(2\le a<n),\qquad
 W_1=\sqrt[n]{\delta\prod_{a=2}^{n-1}R_a}\ \text{(the real root)},
 \qquad W_a=\frac{W_1^a}{\prod_{j=2}^aR_j},\quad W_0=-1.""",
     r""" \begin{gathered}
 R_a=\delta/u_a\quad(2\le a<n),\qquad
 W_1=\sqrt[n]{\delta\prod_{a=2}^{n-1}R_a}\ \text{(the real root)},\\
 W_a=\frac{W_1^a}{\prod_{j=2}^aR_j},\quad W_0=-1.
 \end{gathered}"""),
    (r""" \boxed{\displaystyle
 \int_{-i\infty}^{i\infty}
 \frac{\prod_{i=1}^3S_*(B+z+a_i)S_*(B-z+c_i)}
      {\prod_{i=1}^2
       2\sin(\pi(z+a_i)/B)\,2\sin(\pi(c_i-z)/B)}
 \frac{dz}{i\sqrt{AB}}
 =
 \frac{2\sin(\pi(A-a_3-c_3)/B)}
      {\prod_{i,j=1}^2 2\sin(\pi(a_i+c_j)/B)}
 \prod_{i,j=1}^3 S_*(B+a_i+c_j).}""",
     r""" \boxed{\begin{gathered}
 \int_{-i\infty}^{i\infty}
 \frac{\prod_{i=1}^3S_*(B+z+a_i)S_*(B-z+c_i)}
      {\prod_{i=1}^2
       2\sin(\pi(z+a_i)/B)\,2\sin(\pi(c_i-z)/B)}
 \frac{dz}{i\sqrt{AB}}\\
 {}=\frac{2\sin(\pi(A-a_3-c_3)/B)}
      {\prod_{i,j=1}^2 2\sin(\pi(a_i+c_j)/B)}
 \prod_{i,j=1}^3 S_*(B+a_i+c_j).
 \end{gathered}}"""),
]

WIDE_BOX_NEW = ('\\begin{gathered}\n'
                '\\text{Cyclic Haagerup--Izumi Q-system \\(F\\)-symbols are}\\\\\n'
                r'\text{class-field-theoretic objects over }\;'
                'K_p=\\mathbb Q(\\sqrt{p^2+4}).\n\\end{gathered}')

# The source occasionally drops the backslash in \left( / \right).  Repair
# it rather than emitting math that will not compile.  The lookahead avoids
# touching an ordinary word "left" inside \text{...}.
BAD_DELIM = re.compile(r'(?<![\\A-Za-z])(left|right)(?=[()\[\].])')

sec_no = sub_no = 0

def is_block_start(ls, i):
    l, s = ls[i], ls[i].strip()
    return (not s or HEAD.match(s) or FENCE.match(l) or HRULE.match(l)
            or s == r'\[' or s.startswith('>') or ITEM.match(l)
            or (s.startswith('|') and i + 1 < len(ls) and TSEP.match(ls[i + 1]))
            or s.startswith(BEG) or s.startswith(END))

def split_row(line):
    s = line.strip().strip('|')
    return s.split('|')

# Rough printed widths, in points at \small, used to lay out wide tables.
CH_PT, TOK_PT, MEASURE_PT = 4.6, 4.9, 430.0

def _cellparts(cell):
    """(estimated width, widest unbreakable token) for a Markdown table cell."""
    def mathw(m):
        inner = re.sub(r'\\[A-Za-z]+', 'x', m.group(0)[2:-2])
        return 'M' * max(1, int(len(re.sub(r'[{}\\\\^_ ]', '', inner)) * 1.25))
    t = re.sub(r'\\\\\(.*?\\\\\)', mathw, cell.strip(), flags=re.S)
    t = re.sub(r'[*`\[\]]', '', t)
    tok = max([len(w) for w in t.split()] or [1])
    return len(t), tok

def render_table(rows, align_row):
    letters = []
    for cell in align_row:
        c = cell.strip()
        letters.append('c' if (c.startswith(':') and c.endswith(':'))
                       else ('r' if c.endswith(':') else 'l'))
    cols = len(letters)
    parts = [[_cellparts(r[c]) for r in rows if c < len(r)] for c in range(cols)]
    est = [max([p[0] for p in col] or [1]) * CH_PT for col in parts]
    mins = [max([p[1] for p in col] or [1]) * TOK_PT for col in parts]
    gaps = 12.0 * (cols - 1)
    avail = MEASURE_PT - gaps

    if sum(est) <= avail or sum(mins) > avail:
        return _table_body(rows, ''.join(letters))

    # Proportional shares, but never below the widest unbreakable token in a
    # column: pin those columns first, then split what is left.
    pinned = [False] * cols
    for _ in range(cols):
        free = [c for c in range(cols) if not pinned[c]]
        rem = avail - sum(mins[c] for c in range(cols) if pinned[c])
        tot = sum(est[c] for c in free) or 1.0
        newly = [c for c in free if est[c] / tot * rem < mins[c]]
        if not newly:
            break
        for c in newly:
            pinned[c] = True
    free = [c for c in range(cols) if not pinned[c]]
    rem = avail - sum(mins[c] for c in range(cols) if pinned[c])
    tot = sum(est[c] for c in free) or 1.0
    alloc = [mins[c] if pinned[c] else est[c] / tot * rem for c in range(cols)]

    place = {'l': r'\raggedright', 'r': r'\raggedleft', 'c': r'\centering'}
    spec = ''.join(
        r'>{%s\arraybackslash}p{\dimexpr %.4f\linewidth-%.2fpt\relax}'
        % (place[a], w / avail, gaps * w / avail)
        for a, w in zip(letters, alloc))
    return _table_body(rows, spec)

def _table_body(rows, spec):
    out = ['\\begin{center}\\small',
           '\\begin{tabular}{@{}' + spec + '@{}}', '\\toprule',
           ' & '.join(inline(c.strip()) for c in rows[0]) + ' \\\\', '\\midrule']
    for r in rows[1:]:
        out.append(' & '.join(inline(c.strip()) for c in r) + ' \\\\')
    return '\n'.join(out + ['\\bottomrule', '\\end{tabular}', '\\end{center}'])

def render(ls):
    global sec_no, sub_no
    chunks, i, blank, n = [], 0, True, len(ls)
    while i < n:
        line = ls[i]
        s = line.strip()
        if not s:
            blank = True; i += 1; continue

        if s.startswith(BEG) or s.startswith(END):
            chunks.append((s[5:], blank)); blank = False; i += 1; continue

        m = HEAD.match(s)
        if m:
            level = len(m.group(1))
            title = re.sub(r'^\d+(\.\d+)*\.?\s*', '', m.group(2))
            body = inline(title, xref=False)
            if '\\(' in title:
                body = '\\texorpdfstring{%s}{%s}' % (body, pdfstring(title))
            if level == 1:
                sec_no += 1; sub_no = 0
                SECTION_LABELS.add(str(sec_no))
                chunks.append(('\\section{%s}\\label{sec:%d}' % (body, sec_no), blank))
            elif level == 2 and title == 'Files from this exploration':
                chunks.append(('\\section*{%s}\n\\sloppy' % body, blank))
            elif level == 2:
                sub_no += 1
                SECTION_LABELS.add('%d.%d' % (sec_no, sub_no))
                chunks.append(('\\subsection{%s}\\label{sec:%d.%d}' % (body, sec_no, sub_no), blank))
            else:
                chunks.append(('\\subsubsection*{%s}' % body, blank))
            blank = False; i += 1; continue

        if FENCE.match(line):
            j, buf = i + 1, []
            while j < n and not FENCE.match(ls[j]):
                buf.append(ls[j]); j += 1
            chunks.append(('\\begin{code}\n' + '\n'.join(buf) + '\n\\end{code}', blank))
            blank = False; i = j + 1; continue

        if HRULE.match(line):
            i += 1; blank = True; continue

        if s == r'\[':
            j, buf = i + 1, []
            while j < n and ls[j].strip() != r'\]':
                buf.append(ls[j]); j += 1
            body = '\n'.join(buf).replace('\u2013', '--').replace('\u2014', '---')
            body = body.replace(WIDE_BOX_OLD, WIDE_BOX_NEW)
            for _a, _b in DISPLAY_REFLOWS:
                body = body.replace(_a, _b)
            body, nfix = BAD_DELIM.subn(r'\\\1', body)
            if nfix:
                sys.stderr.write('note: source line %d writes "left("/"right)" '
                                 'without a backslash; repaired %d occurrence(s)\n'
                                 % (i + 1, nfix))
            if '\\tag{' in body or '\\begin{split}' in body:
                chunks.append(('\\begin{equation*}\n' + body + '\n\\end{equation*}', blank))
            else:
                chunks.append(('\\[\n' + body + '\n\\]', blank))
            blank = False; i = j + 1; continue

        if s.startswith('|') and i + 1 < n and TSEP.match(ls[i + 1]):
            head, align, j, rows = split_row(ls[i]), split_row(ls[i + 1]), i + 2, []
            rows.append(head)
            while j < n and ls[j].strip().startswith('|'):
                rows.append(split_row(ls[j])); j += 1
            chunks.append((render_table(rows, align), blank))
            blank = False; i = j; continue

        if s.startswith('>'):
            j, buf = i, []
            while j < n and ls[j].strip().startswith('>'):
                buf.append(re.sub(r'^\s*>\s?', '', ls[j])); j += 1
            chunks.append(('\\begin{mdquote}\n' + render(buf) + '\n\\end{mdquote}', blank))
            blank = False; i = j; continue

        m = ITEM.match(line)
        if m:
            indent, ordered = len(m.group(1)), m.group(2)[0].isdigit()
            items, cur, j = [], None, i
            while j < n:
                lj = ls[j]
                if not lj.strip():
                    k = j
                    while k < n and not ls[k].strip():
                        k += 1
                    cont = False
                    if k < n:
                        mk = ITEM.match(ls[k])
                        cont = ((mk and len(mk.group(1)) >= indent) or
                                (len(ls[k]) - len(ls[k].lstrip()) > indent))
                    if not cont:
                        break
                    if cur is not None:
                        cur.append('')
                    j = k; continue
                mj = ITEM.match(lj)
                if mj and len(mj.group(1)) == indent:
                    cur = [mj.group(3)]; items.append(cur); j += 1; continue
                if mj and len(mj.group(1)) < indent:
                    break
                if cur is not None and (len(lj) - len(lj.lstrip()) > indent or not mj):
                    strip = indent + 2
                    cur.append(lj[strip:] if not lj[:strip].strip() else lj.lstrip())
                    j += 1; continue
                break
            env = 'enumerate' if ordered else 'itemize'
            out = ['\\begin{%s}' % env]
            for it in items:
                body, mark = '\n'.join(it), ''
                mb = re.match(r'^\[([ xX])\]\s+', body)
                if mb:
                    mark = '[$\\boxtimes$]' if mb.group(1).lower() == 'x' else '[$\\square$]'
                    body = body[mb.end():]
                out.append('\\item' + mark + ' ' + render(body.split('\n')).lstrip())
            out.append('\\end{%s}' % env)
            chunks.append(('\n'.join(out), blank))
            blank = False; i = j; continue

        # Defensive: is_block_start must never claim a line that no branch
        # above consumes, or this loop would not advance.
        if is_block_start(ls, i):
            sys.stderr.write('warning: unhandled block at line %r; '
                             'treated as text\n' % ls[i][:60])
            chunks.append((inline(s), blank))
            blank = False; i += 1; continue
        j, buf = i, []
        while j < n and not is_block_start(ls, j):
            buf.append(ls[j]); j += 1
        # Convert the paragraph as a whole: inline math may span two lines.
        HARD = '\x12'
        para = []
        for k, l in enumerate(buf):
            t = l.strip()
            if l.endswith('  ') and k < len(buf) - 1:
                t += HARD
            para.append(t)
        chunks.append((inline('\n'.join(para)).replace(HARD, ' \\\\'), blank))
        blank = False; i = j

    out = []
    for k, (txt, bb) in enumerate(chunks):
        if k and bb:
            out.append('')
        out.append(txt)
    return '\n'.join(out)

# ------------------------------------------------------------ front matter --
title_md = HEAD.match(lines[0]).group(2)
start_body = next(k for k, l in enumerate(lines) if l.startswith('# 1. '))

revgroups, cur = [], []
for l in lines[:start_body]:
    if l.strip().startswith('>'):
        cur.append(re.sub(r'^\s*>\s?', '', l))
    elif cur:
        revgroups.append(cur); cur = []
if cur:
    revgroups.append(cur)

ABSTRACT = r"""These notes summarize the current working picture for cyclic
Haagerup--Izumi fusion categories in the transparent gauge, with emphasis on
(1)~reducing the \(F\)-symbol system to one core matrix \(A\);
(2)~the exact algebraic reconstruction for the \(\mathbb Z_{17}\) Q-system branch;
(3)~evidence that the generic \(F\)-symbol field is a ray class field of
\(K_p=\mathbb Q\!\left(\sqrt{p^2+4}\right)\);
(4)~the candidate relation between normalized \(F\)-symbols and Stark units;
(5)~reproducible PARI/GP tests and the remaining analytic construction problem;
and (6)~exact construction without Haagerup--Izumi seeds, uniform cocycle and
sign reductions, and an infinite family of arithmetic inputs over one quadratic
field.  Some statements below are exact consequences of the transparent-gauge
identities or of exact algebraic manipulations.  Others are computational
conjectures based on reconstruction from published Evans--Gannon numerical
seeds and should be independently verified."""

PREAMBLE = r"""\documentclass[11pt,reqno]{amsart}

\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,array}
\usepackage{fancyvrb}
\usepackage{microtype}
\usepackage[a4paper,left=1.05in,right=1.05in,top=1.2in,bottom=1.2in]{geometry}
\usepackage{xcolor}
\definecolor{linknavy}{RGB}{20,60,120}
\definecolor{linkplum}{RGB}{130,35,70}
\usepackage[colorlinks=true,linkcolor=linknavy,urlcolor=linkplum,
            citecolor=linknavy,bookmarksnumbered=true]{hyperref}

\allowdisplaybreaks
\setlength{\emergencystretch}{1.5em}

\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{conjecture}[theorem]{Conjecture}

\DefineVerbatimEnvironment{code}{Verbatim}%
  {fontsize=\small,xleftmargin=1.6em}

% Displayed statements quoted in the body.
\newenvironment{mdquote}%
  {\par\addvspace{0.5\baselineskip}\begingroup
   \advance\leftskip by 1.6em \advance\rightskip by 1.6em \noindent\ignorespaces}%
  {\par\endgroup\addvspace{0.5\baselineskip}}

% Dated status notes carried over from the source handoff.
\newenvironment{revnote}%
  {\par\addvspace{0.7\baselineskip}\begingroup\small
   \advance\leftskip by 1.2em \advance\rightskip by 1.2em \noindent\ignorespaces}%
  {\par\endgroup\addvspace{0.7\baselineskip}}

\renewcommand{\labelitemi}{\textendash}

\hypersetup{%
  pdftitle={Haagerup-Izumi Zn: transparent F-symbols, class fields,
            and the Stark-unit route},
  pdfsubject={Research notes}}

\begin{document}
"""

# Pre-scan the headings so that forward cross-references resolve too.
_s = _u = 0
for _l in lines[start_body:]:
    _m = HEAD.match(_l.strip())
    if _m and not _l.startswith(' '):
        if len(_m.group(1)) == 1:
            _s += 1; _u = 0
            SECTION_LABELS.add(str(_s))
        elif len(_m.group(1)) == 2 and 'Files from this exploration' not in _m.group(2):
            _u += 1
            SECTION_LABELS.add('%d.%d' % (_s, _u))

body = render(lines[start_body:])

front = [PREAMBLE,
         '\\title[Haagerup--Izumi class fields and Stark units]{%s}'
         % inline(title_md, xref=False),
         '\\date{5 September 2026}', '',
         '\\begin{abstract}', ABSTRACT, '\\end{abstract}', '',
         '\\maketitle', '', '\\tableofcontents', '',
         '\\section*{Revision notes}', '']
front.append('\n\n'.join('\\begin{revnote}\n%s\n\\end{revnote}' % render(g)
                         for g in revgroups))
front.append('')

doc = re.sub(r'\n{3,}', '\n\n', '\n'.join(front) + '\n' + body + '\n\n\\end{document}\n')
doc = doc.replace(QEDMARK, r'\hfill\qedsymbol')
open(OUT, 'w', encoding='utf-8').write(doc)
print('wrote', OUT, len(doc), 'bytes')
