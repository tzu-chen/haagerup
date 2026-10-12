#!/usr/bin/env python3
"""Build the dependency flowchart of the expanded c=8 Haagerup CFT draft.

The flowchart maps the argument of
    c8_expanded_20260929/haagerup_c8_expanded.pdf   (341 pages)
Every reference tag (theorem number and page) is read from that draft's
.aux and .toc files, and every tag is a link to the corresponding named
destination in the draft PDF.

Pipeline:
  1. read labels (.aux) and table-of-contents entries (.toc) of the draft;
  2. typeset every node once to measure its size;
  3. lay out each page with Graphviz `dot`, using the measured sizes;
  4. write hi_cft_c8_dependency_flowchart.tex with explicit coordinates;
  5. compile it twice into a scratch directory and copy the PDF here.

Usage (from the repository root):
    python hi_cft_c8_dependency_flowchart.py            # write .tex and build PDF
    python hi_cft_c8_dependency_flowchart.py --tex-only # write .tex only

The written .tex is self-contained (TikZ with explicit coordinates); it can be
edited by hand, but rerunning this script regenerates it from the page
specifications below.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DRAFT_DIR = "c8_expanded_20260929"
DRAFT = "haagerup_c8_expanded"
DRAFT_PDF = f"{DRAFT_DIR}/{DRAFT}.pdf"
OUT_BASE = "hi_cft_c8_dependency_flowchart"

# ---------------------------------------------------------------------------
# Reading the draft's labels
# ---------------------------------------------------------------------------


def _balanced(s, i):
    """Return (content, index after) for the brace group starting at s[i]."""
    assert s[i] == "{", s[i:i + 20]
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
    raise ValueError("unbalanced braces")


def read_aux(path):
    labels = {}
    text = open(path, encoding="utf-8", errors="replace").read()
    for m in re.finditer(r"\\newlabel\{([^}]*)\}", text):
        name = m.group(1)
        if name.endswith("@cref"):
            continue
        body, _ = _balanced(text, m.end())
        fields = []
        i = 0
        while i < len(body) and len(fields) < 5:
            if body[i] == "{":
                f, i = _balanced(body, i)
                fields.append(f)
            else:
                i += 1
        if len(fields) >= 4:
            labels[name] = (fields[0], fields[1], fields[3])
    return labels


def read_toc(path):
    entries = {}
    text = open(path, encoding="utf-8", errors="replace").read()
    for m in re.finditer(r"\\contentsline\s*\{(\w+)\}", text):
        i = m.end()
        try:
            title, i = _balanced(text, i)
            page, i = _balanced(text, i)
            anchor, i = _balanced(text, i)
        except (AssertionError, ValueError):
            continue
        n = re.search(r"\\numberline\s*\{([^}]*)\}", title)
        if n:
            entries[n.group(1)] = (n.group(1), page, anchor)
    return entries


LABELS = {}
TOC = {}


def resolve(key):
    if key in LABELS:
        return LABELS[key]
    if key in TOC:
        return TOC[key]
    raise KeyError(f"unknown reference key {key!r}")


def link(anchor, text):
    return r"\fclink{%s}{%s}" % (anchor, text)


def tag(ref):
    """Format one reference.

    ref = (prefix, key)               -> 'Lemma C.1 . p. 41'
          (prefix, key, suffix)       -> 'Input F.1(3) . p. 46'
          (prefix, key, None, key2)   -> 'Eqs. 95--97 . p. 42'
    """
    prefix, key = ref[0], ref[1]
    suffix = ref[2] if len(ref) > 2 and ref[2] else ""
    num, page, anchor = resolve(key)
    if len(ref) > 3:
        num = f"{num}--{resolve(ref[3])[0]}"
    sep = r"\," if prefix.endswith("\\S") else "~"
    text = f"{prefix}{sep}{num}{suffix}, p.\\," + page
    return link(anchor, text)


def tags(refs):
    return r";\fcsep ".join(tag(r) for r in refs)


# ---------------------------------------------------------------------------
# Page specifications
# ---------------------------------------------------------------------------

KINDS = {
    "fin": "Finite input",
    "arg": "Argument in draft",
    "con": "Conclusion",
    "ext": "External input",
    "opt": "Optional route",
    "open": "Open boundary",
    "aid": "Checking aid",
}
TYPE_LABEL = {
    "fin": "FINITE INPUT",
    "arg": "ARGUMENT",
    "con": "CONCLUSION",
    "ext": "EXTERNAL THEOREMS",
    "opt": "OPTIONAL ROUTE",
    "open": "OPEN BOUNDARY",
    "aid": "CHECKING AID",
}


class Node:
    def __init__(self, nid, kind, title, body="", refs=(), details=(),
                 label=None):
        self.id = nid
        self.kind = kind
        self.title = title
        self.body = body
        self.refs = list(refs)
        self.details = list(details)
        self.label = label or TYPE_LABEL[kind]

    def content(self):
        parts = [r"{\fctitle %s}" % self.title]
        if self.body:
            parts.append(r"{\fcbody %s}" % self.body)
        if self.refs:
            parts.append(r"{\fctag %s}" % tags(self.refs))
        if self.details:
            parts.append(r"{\fcdetail Details: %s}" % tags(self.details))
        return (r"{\fctype %s}\\[-.6pt]" % self.label) + r"\\".join(parts)


class Edge:
    def __init__(self, a, b, style="dep", label=None, constraint=True,
                 weight=None):
        self.a, self.b = a, b
        self.style = style
        self.label = label
        self.constraint = constraint
        self.weight = weight


class Page:
    def __init__(self, key, title, subtitle, orientation, width_cm, nodes,
                 edges, notes, ranks=(), dot_attrs=None, kinds=None,
                 grid=None, colsep=5.4, rowsep=3.0):
        self.key = key
        self.title = title
        self.subtitle = subtitle
        self.orientation = orientation
        self.width_cm = width_cm
        self.nodes = nodes
        self.edges = edges
        self.notes = notes
        self.ranks = ranks
        self.dot_attrs = dot_attrs or {}
        self.kinds = kinds
        self.grid = grid          # {node id: (column, row)}; rows go down
        self.colsep = colsep      # cm between column centres
        self.rowsep = rowsep      # cm between row centres


N, E = Node, Edge
S = r"\S"   # section-sign prefix for supplementary references

# ----- page 1: overview ----------------------------------------------------

P1 = Page(
    "overview", "Argument overview",
    r"The construction, the net realization, the VOA realization and the "
    r"observables have different dependencies. Teal lines name the "
    r"supplementary appendices that print the supporting data.",
    "portrait", 4.8,
    [
        N("lat", "fin", "Actual lattice subalgebra",
          r"$U=\langle\mathcal K,\omega_B,u\rangle\subset B\subset H=V_{E_8}$\\"
          r"fields, transported PCT, inherited positive form",
          [("Eq.", "eq:U"), ("App.", "sec:construction")],
          [(S, "S2"), (S, "expfinite:reference"), (S, "expdata:coordinates")]),
        N("prop", "con", r"Finite closure $\Rightarrow$ properness",
          r"strong generators of weight $\le4$\\"
          r"$\dim U_1=6$; $U_2=S_2$, $U_3=S_3$",
          [("Prop.", "prop:mainproper"), ("Apps.", "sec:finite", None,
                                          "sec:properness")],
          [(S, "sec:reader-finite"), (S, "expfinite:reference")]),
        N("rat", "con", r"Positive stresses $\Rightarrow$ rationality",
          r"embedded regular factors; $C_2$-cofinite,\\"
          r"projective vacuum; independent of properness",
          [("Thm.", "thm:positive-stress-rationality")],
          [(S, "hr:positive-stress-check"), (S, "hr:structural-inputs")]),
        N("branch", "arg", "Branching and boundary fusion ring",
          r"$B{\downarrow}_U=U\oplus X$, $H{\downarrow}_U=\mathbf1\oplus X\oplus2Y$\\"
          r"rank four excluded; $\mathrm{HI}(\mathbb Z_3)$ ring with $m=1$;\\"
          r"twelve central simples",
          [("App.", "sec:branching")],
          [(S, "expstructure:atlas"), (S, "expstructure:tops"),
           (S, "expstructure:categorical-diagnostics"),
           (S, "expdata:top-atlas")]),
        N("chars", "con", "Complete character vector",
          r"principal-part uniqueness;\\"
          r"$\dim U_1=6+13\gamma$ forces $\gamma=0$",
          [("Lemma", "lem:haagerup-character-unique"),
           ("Eq.", "eq:vacuum-character")],
          [(S, "expdata:characters")]),
        N("netcmp", "arg", "Net and module comparison",
          r"A2: independent count of twelve net sectors\\"
          r"A3: reverse reconstruction, fully faithful",
          [("Prop.", "clm:analytic-net-count"),
           ("Prop.", "clm:analytic-reconstruction")],
          [(S, "expstructure:analytic-map")]),
        N("strong", "con", "Strong VOA unitarity",
          r"all simple modules unitarizable;\\"
          r"twelve net sectors exhaust twelve modules",
          [("Prop.", "prop:analytic-strong-unitarity")]),
        N("netH", "con", "Haagerup net realization",
          r"$\mathrm{Rep}(\mathcal N_U)\simeq Z(\mathcal H_3)$\\"
          r"unitary classification; no A1",
          [("Cor.", "cor:analytic-net-haagerup")]),
        N("a1", "arg", "Pairwise annulus comparison",
          r"A1: bounded insertions agree with\\module vertex operators",
          [("Prop.", "clm:analytic-annulus")],
          [(S, "S14.2"), (S, "S14.3")]),
        N("diag", "con", "Diagonal full net theory",
          r"$Z=\sum_i|\chi_i|^2$; $c_L=c_R=8$",
          [("Prop.", "prop:analytic-diagonal")]),
        N("netext", "con", "Chosen holomorphic net extension",
          r"$\mathcal N_U\subset\mathcal E_3$ of index $\mathrm{Dim}\,\mathcal H_3$;\\"
          r"not identified with the $E_8$ lattice net",
          [("Cor.", "cor:analytic-net-extension")]),
        N("complete", "con", "Complete VOA unitarity",
          r"positive canonical fusion pairings",
          [("Thm.", "thm:analytic-complete-unitarity")]),
        N("voacat", "con", "Unitary VOA category",
          r"$\mathrm{Rep}(U)\simeq Z(\mathcal H_3)$ (unitary ribbon);\\"
          r"original $H/U$: $\mathcal H_2$ or $\mathcal H_3$",
          [("Thm.", "thm:analytic-category")]),
        N("e8ext", "con", r"Chosen $E_8$ VOA extension",
          r"canonical $\mathcal H_3$ algebra gives $H'\cong V_{E_8}$;\\"
          r"$U$-preserving defects $\mathcal H_3\boxtimes\mathcal H_3^{\mathrm{op}}$",
          [("Thm.", "thm:analytic-e8-extension")]),
        N("thm13", "con", r"Theorem 1.3: net realization",
          r"assembled from Thm.~F.8, Prop.~I.4,\\Cor.~J.3 and Prop.~K.2",
          [("Thm.", "thm:main-net")], label="MAIN THEOREM"),
        N("thm14", "con", r"Theorem 1.4: VOA realization",
          r"and holomorphic extension; assembled\\from Thms.~I.8, J.2 and K.3",
          [("Thm.", "claim:main")], label="MAIN THEOREM"),
        N("phys", "con", "Physical data",
          r"spectra, thermal quantities, OPEs,\\"
          r"defects, boundaries, bootstrap coordinates",
          [("Secs.", "sec:physics-spectrum", None, "sec:physics-data-guide")],
          [(S, "expphysics:interaction-atlas", None,
            "expphysics:extension-details"),
           (S, "expdata:characters", None, "expdata:thermal")]),
        N("ledger", "aid", "Ledger, replays and Lean scope",
          r"finite records and their fresh replays;\\"
          r"Lean covers selected abstract steps only",
          [("App.", "sec:ledger"), (S, "M.1"),
           ("App.", "sec:formalization")],
          [(S, "expstructure:provenance"), (S, "sec:review-lean")]),
    ],
    [
        E("lat", "prop"), E("lat", "rat"),
        E("prop", "branch"), E("rat", "branch"),
        E("prop", "chars", label=r"$\dim U_1=6$"), E("branch", "chars"),
        E("branch", "netcmp"), E("rat", "netcmp", label="regularity"),
        E("netcmp", "strong"), E("netcmp", "netH"), E("netcmp", "a1"),
        E("netcmp", "diag"), E("chars", "diag", label="characters for $Z$"),
        E("strong", "complete"), E("a1", "complete"),
        E("netH", "netext"),
        E("complete", "voacat"), E("branch", "voacat", label="fusion ring"),
        E("voacat", "e8ext"),
        E("strong", "thm13", style="thin"),
        E("netH", "thm13", style="thin"), E("diag", "thm13", style="thin"),
        E("complete", "thm14", style="thin"), E("voacat", "thm14", style="thin"),
        E("e8ext", "thm14", style="thin"),
        E("lat", "phys", label="direct lattice OPEs", constraint=False),
        E("chars", "phys"), E("diag", "phys"), E("e8ext", "phys"),
        E("ledger", "prop", style="aid"), E("ledger", "rat", style="aid"),
    ],
    [
        r"Arrows show selected logical dependencies, not chronology. "
        r"Incoming arrows are used jointly; transitive dependencies are "
        r"usually omitted. Thin arrows show how the two main theorems are "
        r"assembled. Pages 2--7 resolve each block into its steps.",
    ],
    grid={
        "ledger": (0, 0), "lat": (2, 0),
        "prop": (1, 1), "rat": (3, 1),
        "branch": (2, 2),
        "chars": (0.5, 3), "netcmp": (2.5, 3),
        "diag": (0, 4), "netH": (1, 4), "strong": (2.1, 4), "a1": (3.3, 4),
        "netext": (1, 5), "complete": (2.7, 5),
        "thm13": (0.4, 6), "voacat": (3.3, 6),
        "e8ext": (3.3, 7),
        "phys": (1.2, 8), "thm14": (2.6, 8),
    },
    colsep=6.0, rowsep=3.45,
)

# ----- page 2: finite construction -----------------------------------------

P2 = Page(
    "finite", "Finite construction and the all-weight argument",
    r"Appendices A--E: actual-vector provenance comes before closure, the "
    r"two gates are derived from finite witnesses, and properness comes "
    r"before any character identification.",
    "portrait", 4.7,
    [
        N("amb", "fin", "Ambient lattice VOA",
          r"$B=V_{E_6\oplus A_2}\subset H=V_{E_8}$;\\cocycle and mode formula",
          [("Eq.", "eq:cocycle"), ("Eq.", "eq:lattice-product")],
          [(S, "expfinite:coordinates"), (S, "expfinite:mode-engine")]),
        N("lev", "arg", "Two affine levels",
          r"the two current triples generate\\"
          r"$A_{1,1}\otimes A_{1,39}$; $K=\mathcal K_1$, $\dim K=6$",
          [("Lemma", "lem:levels")]),
        N("ufield", "fin", "Defining field and real form",
          r"$u$: three momenta, fixed relative phase;\\"
          r"transported PCT $\theta_g$; stress $\omega_B$",
          [("Eq.", "eq:u"), ("Eq.", "eq:pct")],
          [(S, "hr:three-term-vector"), (S, "expdata:coordinates")]),
        N("mingen", "fin", "Minimal generation",
          r"$K,\omega_B,u$ generate all $120$ vectors\\"
          r"of $S_2$ under current zero modes and $u_1$",
          [(S, "A.3")],
          [(S, "S4.2"), (S, "expfinite:generation-graph")]),
        N("init", "fin", "Initial spaces",
          r"$\dim S_2=120$, $\dim S_3=956$,\\"
          r"$\dim N_3=634$; $P=S_3/N_3$ has dimension $322$",
          [("Input", "cert:initial")],
          [(S, "expfinite:complete-fields"), (S, "expfinite:grade-three")]),
        N("lower", "fin", "Lower identities and triplet",
          r"3,970 exact identities; actual $P_4$;\\"
          r"$L(1)P_4\subset S_3$, $L(2)P_4\subset S_2$",
          [("Input", "cert:lower")],
          [(S, "expfinite:3970"), (S, "expfinite:actual-triplet")]),
        N("bounds", "arg", "Current projector bounds",
          r"Cartan eigenvalues $m^2\le2d(h,h)$;\\"
          r"finite $FE$ polynomials are exact projectors",
          [("Lemma", "lem:current-bounds")]),
        N("g4pack", "fin", "Gate 4 certificate packet",
          r"2,145 + 118 + 12 seed identities;\\"
          r"644 raising images (rank 294); nine ranks 322;\\"
          r"12 projected residuals on 21 columns",
          [("App.", "sec:gate4")],
          [(S, "S4.3"), (S, "expfinite:gate4-inventory"),
           (S, "expfinite:projected-columns")]),
        N("raise", "arg", "Raising saturation",
          r"$P=E_LP+E_RP+C_a$ forces $f_a=0$;\\"
          r"raising words of length 25 vanish",
          [("Lemma", "lem:raising")]),
        N("singlet", "arg", "Joint-singlet recovery",
          r"the twelve weight-$(0,0)$ classes are\\"
          r"recovered through the projector $\Pi$",
          [("Lemma", "lem:singlet"), ("Eq.", "eq:projector")]),
        N("gate4", "con", "Gate 4",
          r"$(S_2)_0S_3\subset W_4$: all $9\cdot322=2898$\\"
          r"highest-left identities",
          [("Eq.", "eq:gate4")]),
        N("boot", "arg", "Positive-mode bootstrap",
          r"controls on $S_3$, $W_4$ and $N_5$,\\"
          r"established before Gate 5",
          [("Lemma", "lem:bootstrap"),
           ("Eqs.", "eq:positive-S3", None, "eq:positive-N5")]),
        N("normal", "arg", "Normal-space controls",
          r"$(S_2)_0N_4,\ (N_3)_0S_3\subset N_5$;\\"
          r"no $P_3$-by-$P_3$ closure is used",
          [("Lemma", "lem:normal-controls")]),
        N("jacobi", "arg", "Jacobi reduction",
          r"$F(a,\beta(b,p))=F(b,\beta(a,p))$\\whenever $a_0b\in N_3$",
          [("Lemma", "lem:jacobi")]),
        N("g5pack", "fin", "Gate 5 bottom witnesses",
          r"$\beta(a_3,p_3)=c_3q_-$, $\beta(a_6,p_6)=c_6q_-$,\\"
          r"$c_3c_6\neq0$; table of $(a_i)_0a_j\in N_3$",
          [(S, "D.1")],
          [(S, "S4.4")]),
        N("span", "fin", "Charged-span certificate",
          r"28 reconstructed charged seeds and\\"
          r"644 lowering images span all of $P$",
          [(S, "D.2")],
          [(S, "expfinite:gate5-seeds")]),
        N("charged", "arg", "Charged families",
          r"weight exclusion at the bottom inputs,\\"
          r"then raising: 23 channels",
          [(S, "D.1")]),
        N("neutral", "arg", "Neutral family",
          r"$P/C=0$, then $(e_0a_3)_0p_3\in N_5$\\"
          r"by two Jacobi identities: one channel",
          [(S, "D.2")]),
        N("gate5", "con", "Gate 5",
          r"$(S_2)_0P_4\subset N_5$: 24 channels derived,\\"
          r"not recomputed grade-five products",
          [("Eq.", "eq:gate5")]),
        N("finish", "arg", r"Remaining modes on $P_4$",
          r"Virasoro commutators give $a_nP_4$, $n\le4$;\\"
          r"the 30 prime-only tests are derived",
          [("App.", "sec:properness")]),
        N("wick", "arg", "Filtered Wick reduction",
          r"singular products of normal expressions\\"
          r"reduce to generator pairs",
          [("Lemma", "lem:filtered-wick")]),
        N("crit", "arg", "Recursive strong-generation criterion",
          r"(i) $k_ns,a_ns\in\mathcal N$;\ "
          r"(ii) $S_d\subset A_0S_{d-1}+\mathcal N_d$\\"
          r"$\Rightarrow$ $\mathcal N$ is a vertex subalgebra",
          [("Thm.", "thm:recursive"), ("Rem.", "rem:finite-scope")]),
        N("spanU", "con", r"Normal span equals $U$",
          r"Theorem B.3 applies to $K,S_2,S_3,P_4$:\\"
          r"strong generators of weight $\le4$",
          [("App.", "sec:properness")]),
        N("proper", "con", "Properness and low grades",
          r"$U_1=K$: $\dim U_1=6<86=\dim B_1$;\\"
          r"$U_2=S_2$, $U_3=S_3$; PCT-stable, hence\\"
          r"simple and unitary (CKLW); $c=8$",
          [("Prop.", "prop:mainproper"), ("Cor.", "cor:initial-grades")]),
        N("lean", "aid", "Lean-checked abstract steps",
          r"raising saturation, projected-residual\\"
          r"recovery, Jacobi bottom implication",
          [("App.", "sec:formalization")],
          [(S, "S26.3")]),
    ],
    [
        E("amb", "lev"), E("amb", "ufield"),
        E("lev", "mingen"), E("ufield", "mingen"),
        E("mingen", "init"),
        E("init", "lower"), E("init", "g4pack"),
        E("lower", "raise", label=r"$a_0N_3\subset N_4$"),
        E("g4pack", "raise"), E("bounds", "raise", label="nilpotence"),
        E("g4pack", "singlet"), E("bounds", "singlet"),
        E("raise", "gate4"), E("singlet", "gate4"),
        E("lower", "boot"), E("gate4", "boot"),
        E("boot", "normal"), E("gate4", "normal"),
        E("normal", "jacobi"),
        E("jacobi", "charged"), E("g5pack", "charged"),
        E("charged", "neutral"), E("span", "neutral"), E("jacobi", "neutral"),
        E("charged", "gate5"), E("neutral", "gate5"),
        E("boot", "finish"), E("gate5", "finish"),
        E("wick", "crit"),
        E("crit", "spanU"), E("finish", "spanU"),
        E("spanU", "proper"),
        E("lean", "raise", style="aid"), E("lean", "singlet", style="aid"),
        E("lean", "jacobi", style="aid"),
    ],
    [
        r"The projected residuals alone do not prove Gate~4: raising "
        r"premises and saturation ranks are also used. Gate~5 and its "
        r"positive-mode consequences are derived; the value "
        r"$\dim U_4=6010$ is not an input. Every finite input is listed "
        r"with its record in the certificate ledger (App.~M) and its fresh "
        r"replay in \S M.1.",
    ],
    grid={
        "amb": (1.2, 0),
        "lev": (0.5, 1), "ufield": (1.9, 1),
        "mingen": (0.5, 2), "init": (1.9, 2),
        "lower": (0.6, 3), "g4pack": (1.8, 3), "bounds": (3.0, 3),
        "raise": (1.1, 4), "singlet": (2.4, 4), "lean": (3.7, 4),
        "gate4": (1.7, 5),
        "boot": (0.8, 6), "normal": (2.2, 6),
        "jacobi": (1.6, 7), "g5pack": (2.75, 7), "span": (3.9, 7),
        "charged": (2.2, 8), "neutral": (3.4, 8),
        "gate5": (2.8, 9),
        "finish": (1.8, 10), "wick": (4.3, 9.7),
        "spanU": (2.6, 11), "crit": (4.3, 10.9),
        "proper": (2.6, 12),
    },
    colsep=5.4, rowsep=2.5,
)

# ----- page 3: regularity ----------------------------------------------------

P3 = Page(
    "regularity", "Regularity and strong rationality",
    r"Appendix F works with the actual PCT-stable algebra $U\subset B$. "
    r"None of its conclusions uses properness or the finite closure gates.",
    "portrait", 4.9,
    [
        N("vac", "con", "Vacuum unitarity of the actual $U$",
          r"PCT-stable subalgebra of $B$ with the\\"
          r"inherited positive form; simple, CFT type",
          [("Eq.", "eq:pct"), ("Cor.", "cor:initial-grades")]),
        N("potts", "fin", "Potts factor",
          r"Potts fields lie in $U$, are PCT stable and\\"
          r"generate the regular $K(\mathfrak{sl}_2,3)$",
          [("Input", "cert:structural-inputs", "(1)")],
          [(S, "S5.2"), (S, "expdata:coordinates")]),
        N("pfrows", "fin", "Parafermion fields and rows",
          r"$z,a\in U$, $c=8/5$, $\lambda=14/473$; full singular\\"
          r"first rows as normal polynomials",
          [("Input", "cert:structural-inputs", "(2)")],
          [(S, "S5.3"), (S, "hr:membership-words"),
           (S, "expfinite:complete-membership")]),
        N("stress", "fin", "Positive stress identity",
          r"$\omega_U=\omega_{A_{1,1}}+(3403/4563)\,\omega_{A_{1,39}}$\\"
          r"${}+(25/6)\,\overline p+(25/26)\,\overline z$",
          [("Eq.", "eq:positive-stress")],
          [(S, "hr:positive-stress-check"), (S, "S5.5")]),
        N("extpf", "ext", "Parafermion literature",
          r"Linshaw recursive rows; Dong--Lam--Yamada\\"
          r"decoupling coefficients",
          [("Prop.", "prop:pf13-finite-reconstruction")]),
        N("pf", "arg", "Finite reconstruction of the parafermion",
          r"the checked rows of $L,a,b,d$ determine\\"
          r"the algebra: actual $K(\mathfrak{sl}_2,13)\subset U$",
          [("Prop.", "prop:pf13-finite-reconstruction")]),
        N("haar", "arg", r"Averages inside $S_2$",
          r"Haar averages are combinations of four\\"
          r"orthogonal stresses; by Carath\'eodory\\"
          r"$\omega_U=c_1e_1+\dots+c_Ne_N$, all $c_i>0$",
          [("Eq.", "eq:finite-positive-stress")]),
        N("abd", "ext", r"Module $C_2$ quotients",
          r"Abe--Buhl--Dong: finite-dimensional\\for regular algebras",
          [("Lemma", "lem:positive-c2")]),
        N("c2", "arg", "Orthogonal energy bound",
          r"intrinsic energies are bounded on $C_2(V)^\perp$;\\"
          r"hence $U$ is $C_2$-cofinite",
          [("Lemma", "lem:positive-c2")]),
        N("top", "arg", "Highest spaces for a compatible subalgebra",
          r"stable, lowering-killed finite spaces\\are sums of simple tops",
          [("Lemma", "lem:compatible-top")]),
        N("vaclike", "arg", "Vacuum-like vectors",
          r"$L(-1)v=0$ gives a module\\map $V\to M$ sending $\mathbf1\mapsto v$",
          [("Lemma", "lem:vacuum-like")]),
        N("proj", "arg", "Lowest weights; projective vacuum",
          r"trace identity gives $h\ge0$ on every top;\\"
          r"only $V$ has weight $0$; vacuum projective",
          [("Lemma", "lem:vacuum-projective"), ("Eq.", "eq:top-trace")]),
        N("mcrae", "ext", "Finite-category theorems",
          r"McRae: braided Grothendieck--Verdier\\"
          r"module category; Etingof--Penneys: rigidity",
          [("Lemma", "lem:projective-unit")]),
        N("unit", "arg", r"Projective unit in a braided $r$-category",
          r"projective $\mathbf1$ $\Rightarrow$ rigid and semisimple",
          [("Lemma", "lem:projective-unit")]),
        N("rat", "con", "Strong rationality",
          r"$U$ is strongly rational, independently\\"
          r"of properness; no unitarity of modules used",
          [("Thm.", "thm:positive-stress-rationality")]),
        N("later", "con", "Used in Appendices G and I",
          r"semisimple $B{\downarrow}_U$; positive nonvacuum weights;\\"
          r"complete $A_L$ tops (Lemma F.4); regular $U$",
          [("App.", "sec:branching"), ("App.", "sec:analytic-unitarity")]),
    ],
    [
        E("pfrows", "pf"), E("extpf", "pf"),
        E("stress", "haar"),
        E("potts", "c2", label="regular factor"),
        E("pf", "c2", label="regular factor"),
        E("haar", "c2"), E("abd", "c2"), E("vac", "c2"),
        E("top", "proj"), E("vaclike", "proj"), E("c2", "proj"),
        E("haar", "proj"),
        E("mcrae", "unit"),
        E("c2", "rat"), E("proj", "rat"), E("unit", "rat"), E("vac", "rat"),
        E("rat", "later"), E("proj", "later"), E("top", "later"),
    ],
    [
        r"The embedded regular factors and the positive stress identity are "
        r"exact field inputs (review note R1 of App.~F); "
        r"Proposition~F.2 transports the checked parafermion rows to an "
        r"identification but does not replace their verification. Lemma~F.7 "
        r"does not assume that nonvacuum modules are unitarizable.",
    ],
    grid={
        "potts": (0.2, 0), "pfrows": (1.45, 0), "extpf": (2.7, 0),
        "stress": (3.93, 0),
        "vac": (0, 1.45), "pf": (2.0, 1.2), "haar": (3.9, 1.3),
        "abd": (0.5, 2.7), "c2": (1.9, 2.6), "top": (3.2, 2.6),
        "vaclike": (4.0, 3.75),
        "mcrae": (0.3, 3.95), "proj": (2.75, 3.95),
        "unit": (0.6, 5.2), "rat": (1.9, 5.35),
        "later": (2.6, 6.6),
    },
    colsep=5.3, rowsep=3.95,
)

# ----- page 4: branching and the rank fork ------------------------------------

P4 = Page(
    "branching", "Branching and the rank fork",
    r"Appendix G, first half: the actual lattice branching fixes the boundary "
    r"category up to rank four or six, and rank four is excluded before any "
    r"unitary classification is invoked.",
    "portrait", 4.6,
    [
        N("inP", "con", "Proper branch (page 2)",
          r"$\dim U_1=6$; actual $U\subsetneq B$",
          [("Prop.", "prop:mainproper")]),
        N("inR", "con", "Strong rationality (page 3)",
          r"semisimplicity; positive nonvacuum\\"
          r"lowest weights; Lemma F.4 for tops",
          [("Thm.", "thm:positive-stress-rationality"),
           ("Lemma", "lem:compatible-top")]),
        N("corewit", "fin", "Core spectral witnesses",
          r"six joint eigenvectors in $U_2$:\\"
          r"$z_1=12/13$, $(\omega_{\mathcal T})_1=14/13$, $p_1=2/3$",
          [("Input", "cert:structural-inputs", "(3)")],
          [(S, "S5.6"), (S, "expstructure:R-extension"), (S, "S25.1")]),
        N("irr", "fin", "80-current and 81-top irreducibility",
          r"exact zero-mode actions: the complementary\\"
          r"currents and four mixed tops are irreducible",
          [("Input", "cert:structural-inputs", "(4)")],
          [(S, "S5.7"), (S, "expdata:80-top"), (S, "expdata:81-tops")]),
        N("AL", "arg", r"Embedded order-13 core $A_L$",
          r"isotropic charge line $k=\pm5j$;\\"
          r"$\mathrm{Rep}(A_L)\simeq\mathrm{Fib}\boxtimes SO(3)_{13}$, 14 simples",
          [(S, "G.1"), ("Eq.", "eq:core-charge-minimum")],
          [(S, "expstructure:atlas")]),
        N("topb", "arg", "Universal top bound",
          r"trace identity on complete $A_L$ tops:\\"
          r"$0\le h\le17/10<2$ for every simple module",
          [("Eq.", "eq:top-W"), ("Eq.", "eq:sharp-top-bound")],
          [(S, "expstructure:tops"), (S, "S26.3")]),
        N("branchB", "arg", "Actual lattice branching",
          r"$B{\downarrow}_U=U\oplus X$, $h_X=1$;\\"
          r"$H{\downarrow}_U=\mathbf1\oplus X\oplus Y\oplus Y^*$, $h_Y=1$",
          [("Eq.", "eq:B-branching"), ("Eq.", "eq:H-branching-fork")]),
        N("dmno", "ext", "Lagrangian algebras",
          r"DMNO center correspondence;\\"
          r"Bischoff--Jones two products",
          [(S, "G.2")]),
        N("fork", "arg", "Rank four or rank six",
          r"$\mathrm{Rep}(U)\simeq Z(\mathcal F)$, $\mathcal F$ = all $H$-modules;\\"
          r"$\mathrm{rank}\,\mathcal F=\dim\mathrm{End}(H)\in\{4,6\}$",
          [("Eq.", "eq:rank-fork")],
          [(S, "S13.1")]),
        N("inv", "arg", "Three untwisted invertibles",
          r"$\mathbb Z/3$ automorphisms of $H/B$ inject;\\"
          r"$X$ is not invertible;\\"
          r"$L_-$ Tannakian: untwisted $\mathrm{Vec}_{\mathbb Z/3}$",
          [("Lemma", "lem:automorphisms-invertibles"),
           ("Lemma", "lem:no-sign-extension")]),
        N("larson", "ext", "Near-group inputs",
          r"Larson: $m\in\{0,2,3,6\}$; EGO; HKL;\\"
          r"Dong--Mason; DLN; Kirillov--Ostrik",
          [(S, "G.3")]),
        N("m02", "arg", r"Exclude $m=0$ and $m=2$",
          r"$m=0$: $d_X=1$; $m=2$: an $A_4$-orbifold\\"
          r"of $V_{E_8}$ has at least 16 currents",
          [(S, "G.3")]),
        N("ngind", "arg", "Near-group induction",
          r"twist moments; $m=3$ modular data;\\"
          r"$m=6$: balanced case impossible, projection",
          [("Lemma", "lem:near-group-induction"),
           ("Prop.", "prop:m3-modular"), ("Lemma", "lem:m6-balanced"),
           ("Lemma", "lem:m6-projection")],
          [(S, "S13.2")]),
        N("pole", "arg", "Pole cancellation",
          r"no invariant vector: equal principal\\"
          r"parts give equal functions (used again, p.~5)",
          [("Lemma", "lem:pole-cancellation")]),
        N("curr", "arg", "Current obstructions",
          r"theta-series matching puts $\dim U_1$ in\\"
          r"families that never contain $6$",
          [("Prop.", "prop:near-group-current-obstructions")]),
        N("r4out", "con", "Rank four excluded",
          r"$H{\downarrow}_U=\mathbf1\oplus X\oplus2Y$; $\mathcal F$ has rank six\\"
          r"with three untwisted invertibles (page 5)",
          [(S, "G.4")]),
    ],
    [
        E("corewit", "AL"), E("inR", "AL", label="regular factors"),
        E("AL", "topb"), E("inR", "topb"),
        E("topb", "branchB", label="next top weight $2$ excluded"),
        E("irr", "branchB"), E("inR", "branchB"),
        E("inP", "branchB", label="$86-6=80$ currents"),
        E("branchB", "fork"), E("dmno", "fork"),
        E("branchB", "inv"), E("fork", "inv"), E("dmno", "inv"),
        E("inP", "inv", label="rank of $U_1$"),
        E("fork", "m02"), E("inv", "m02"), E("larson", "m02"),
        E("fork", "ngind"), E("inv", "ngind"), E("larson", "ngind"),
        E("ngind", "curr"), E("pole", "curr"),
        E("inP", "curr", label=r"$\dim U_1=6$"),
        E("m02", "r4out"), E("curr", "r4out"),
    ],
    [
        r"Larson's near-group theorem assumes pseudo-unitarity; for "
        r"$\mathcal F$ it follows from that of its center, whose positive "
        r"spherical structure comes from strictly positive nonvacuum lowest "
        r"weights. No $C^*$ structure is used here. Lemma~G.2 replaces the "
        r"earlier pointwise stabilizer computation $\mathrm{Aut}(B/U)=1$.",
    ],
    grid={
        "inP": (0, 0), "inR": (1.25, 0), "corewit": (2.5, 0),
        "irr": (3.95, 0.35),
        "AL": (2.1, 1.1),
        "topb": (2.1, 2.2),
        "branchB": (2.6, 3.3), "dmno": (4.0, 3.3),
        "inv": (1.4, 4.6), "fork": (3.0, 4.5),
        "larson": (4.0, 5.1),
        "pole": (0.1, 5.9), "ngind": (1.6, 6.0), "m02": (3.2, 6.0),
        "curr": (1.2, 7.1),
        "r4out": (2.4, 8.1),
    },
    colsep=5.4, rowsep=3.6,
)

# ----- page 5: rank six, modular data, characters ------------------------------

P5 = Page(
    "characters", "Rank six, modular data and the characters",
    r"Appendix G, second half, and Appendix H: the character proof uses "
    r"modular data derived from the actual branching, not an assumed "
    r"tensor-category identification.",
    "portrait", 4.6,
    [
        N("inP2", "con", "Proper branch (page 2)",
          r"$\dim U_1=6$",
          [("Prop.", "prop:mainproper")]),
        N("in4", "con", "Rank-six boundary category (page 4)",
          r"noncommutative $\mathrm{End}(H)$; three invertibles\\"
          r"with untwisted $\mathrm{Vec}_{\mathbb Z/3}$",
          [("Eq.", "eq:rank-fork"), (S, "G.4")]),
        N("inPole", "arg", "Pole cancellation (page 4)",
          r"equal principal parts give equal\\vector-valued functions",
          [("Lemma", "lem:pole-cancellation")]),
        N("ring6", "arg", "Rank-six ring",
          r"$\mathbb C^2\oplus M_2(\mathbb C)$ forces $\rho a=a^2\rho$ and\\"
          r"$\rho^2=1+m(\rho+a\rho+a^2\rho)$, $m\ge1$",
          [("Eq.", "eq:rank6-ring")]),
        N("ext6", "ext", "Root-of-unity inputs",
          r"Ostrik formal codegrees; Ng--Schauenburg\\"
          r"twist formula; Larson sums of roots",
          [(S, "G.4")]),
        N("ind6", "arg", "Center induction and two moments",
          r"$I(1)=1+X+2Y$; first and second twist\\"
          r"sums of the residual simples",
          [("Lemma", "lem:rank6-induction"),
           ("Eqs.", "eq:indicator-first", None, "eq:indicator-second")]),
        N("mone", "arg", r"Exclude $m>1$",
          r"square-class bound, and the\\"
          r"conductor-forty equality case at $m=2$",
          [("Eq.", "eq:squareclass-bound"), ("Lemma", "lem:conductor40")],
          [(S, "S13.3")]),
        N("hi", "con", r"Spherical untwisted $\mathrm{HI}(\mathbb Z_3)$",
          r"$m=1$, $d=(3+\sqrt{13})/2$;\\"
          r"six residual twists, $\nu_2(\rho)=1$;\\twelve central simples",
          [("Eq.", "eq:haagerup-dimensions"),
           ("Lemma", "lem:six-residual-twists")]),
        N("gsy", "ext", "Modular-data theorem",
          r"Gannon--Schopieray--Yadav, Thm.~A(2);\\"
          r"the prime-13 metric group is fixed",
          [(S, "G.4")]),
        N("st", "con", r"Haagerup $S$ and $T$",
          r"modular representation determined;\\"
          r"not yet a ribbon classification",
          [(S, "G.4")]),
        N("vercl", "opt", "Extra pivotal census",
          r"assume Vercleyen's four-entry\\list is exhaustive",
          [(S, "G.5")]),
        N("ribbon", "opt", "Abstract ribbon identification",
          r"$\mathrm{Rep}(U)\simeq Z(\mathcal H_3)$ abstractly;\\"
          r"no fusion positivity",
          [("Prop.", "prop:optional-algebraic-identification")]),
        N("dln", "ext", "Character-theory inputs",
          r"DLN congruence (finite image);\\"
          r"Evans--Gannon fundamental matrix $\Xi$",
          [("App.", "sec:characters")]),
        N("huniq", "arg", "Uniqueness from the principal part",
          r"no invariant constants for this $(S,T)$",
          [("Lemma", "lem:haagerup-character-unique")]),
        N("chars", "con", "All twelve characters",
          r"$\chi=\Xi_{:,0}+\gamma\,\Xi_{:,d_3}$, $\dim U_1=6+13\gamma$\\"
          r"$\Rightarrow\gamma=0$; lowest weights $\le15/13$",
          [("Eq.", "eq:vacuum-character")],
          [(S, "expdata:characters")]),
        N("unmixed", "con", "Unmixed lattice restrictions",
          r"$(0,\pm1)\mapsto c_1$, $(\pm1,0)\mapsto c_2$",
          [("Cor.", "cor:unmixed-lattice-restrictions")]),
    ],
    [
        E("in4", "ring6"),
        E("ring6", "ind6"), E("in4", "ind6", label="untwisted"),
        E("ext6", "ind6"),
        E("ind6", "mone"), E("ext6", "mone"),
        E("mone", "hi"), E("ind6", "hi"),
        E("hi", "st"), E("gsy", "st"),
        E("hi", "vercl", style="opt"), E("vercl", "ribbon", style="opt"),
        E("in4", "ribbon", style="opt"),
        E("st", "huniq"), E("dln", "huniq"), E("inPole", "huniq"),
        E("huniq", "chars"), E("dln", "chars"),
        E("inP2", "chars", label=r"$\dim U_1=6$"),
        E("chars", "unmixed"),
    ],
    [
        r"Dashed arrows mark an optional route using an extra "
        r"pivotal-classification hypothesis. It is not used for the "
        r"characters or the analytic realization, and it does not establish "
        r"canonical VOA fusion positivity. The character vector fixes every "
        r"graded dimension but was not used to prove properness.",
    ],
    grid={
        "inP2": (0, 0), "in4": (1.6, 0), "ext6": (3.5, 0.6),
        "ring6": (1.6, 1.1),
        "ind6": (2.2, 2.2),
        "mone": (3.3, 3.3),
        "hi": (2.2, 4.4),
        "gsy": (0.6, 4.9), "vercl": (3.7, 5.3),
        "st": (1.5, 5.8), "inPole": (0.0, 3.1),
        "ribbon": (3.7, 6.6),
        "dln": (0.1, 6.6), "huniq": (1.5, 7.0),
        "chars": (1.3, 8.2), "unmixed": (3.0, 8.2),
    },
    colsep=5.4, rowsep=3.6,
)

# ----- page 6: analytic realization -------------------------------------------

P6 = Page(
    "analytic", "Analytic realization: two distinct routes",
    r"Appendices I--K: positivity of the vacuum, of all modules and of the "
    r"fusion pairings are separate assertions; A2--A3 and A1 are different "
    r"bridges.",
    "landscape", 4.55,
    [
        N("alg", "con", "Algebraic inputs (pages 2--4)",
          r"regularity; $H{\downarrow}_U=U\oplus X\oplus2Y$; rank-six\\"
          r"ring with untwisted pointed part;\\"
          r"twelve simple modules; Lemmas G.1--G.2",
          [("Eq.", "eq:analytic-branching"), ("App.", "sec:characters")]),
        N("netthm", "ext", "Lattice and net theorems",
          r"CKLW strong locality; Tener bounded\\"
          r"insertions; Longo finite index",
          [(S, "subsec:analytic-net-count")]),
        N("subnet", "arg", "Completely rational subnet",
          r"$[\mathcal A^{\mathrm{bl}}_H:\mathcal A^{\mathrm{bl}}_U]<\infty$;"
          r" vacuum isomorphism\\transfers rationality to $\mathcal N_U$",
          [(S, "subsec:analytic-net-count")]),
        N("core", "arg", "Reduction on a common core",
          r"domain-invariant projections\\reduce closed fields",
          [("Lemma", "lem:analytic-graph-reduction")],
          [(S, "S14.1")]),
        N("a2a", "arg", "A2: actual net branching",
          r"summands $1,1,2$ stay irreducible;\\"
          r"finite index (Kawahigashi--Longo);\\"
          r"$\mathrm{End}(A_{\mathrm{net}})\cong\mathbb C^2\oplus M_2(\mathbb C)$",
          [("Prop.", "clm:analytic-net-count"),
           ("Eq.", "eq:analytic-end-algebra")]),
        N("a2b", "arg", "A2: net invertibles",
          r"$\mathrm{Inv}(\mathcal F_{\mathrm{net}})=\mathbb Z/3$: index two\\"
          r"excluded via CKLW and Lemma G.2;\\untwisted through $L_-$",
          [("Prop.", "clm:analytic-net-count")]),
        N("a2c", "arg", "A2: twelve net sectors",
          r"rank-six and indicator argument applied\\"
          r"to $\mathcal F_{\mathrm{net}}$; "
          r"$\mathrm{Rep}(\mathcal N_U)\simeq Z(\mathcal F_{\mathrm{net}})$",
          [("Eq.", "eq:analytic-center-dimensions")]),
        N("ht", "ext", "Henriques--Tener reconstruction",
          r"Thm.~9.5, Rem.~9.8 (no finite multiplicity),\\"
          r"Thm.~8.9 (vacuum VOA is $U$)",
          [(S, "subsec:analytic-reconstruction")]),
        N("a3", "arg", "A3: reverse reconstruction",
          r"net sector $\mapsto$ simple ordinary unitary module;\\"
          r"fully faithful linear $*$-functor, no tensorator",
          [("Prop.", "clm:analytic-reconstruction"),
           ("Eq.", "eq:analytic-projection-core")]),
        N("strong", "con", "Strong unitarity",
          r"twelve inequivalent images exhaust\\"
          r"the twelve algebraic simples",
          [("Prop.", "prop:analytic-strong-unitarity")]),
        N("izumi", "ext", "Unitary classification",
          r"Izumi: $\mathcal H_2$ or $\mathcal H_3$; Grossman--Snyder:\\"
          r"one Morita class; Reutter: unitary braiding",
          [("App.", "sec:analytic-category")]),
        N("netH", "con", "Net Haagerup center",
          r"$\mathrm{Rep}(\mathcal N_U)\simeq Z(\mathcal H_3)$; boundary\\"
          r"category of the $E_8$ net: $\mathcal H_2$ or $\mathcal H_3$; no A1",
          [("Cor.", "cor:analytic-net-haagerup")]),
        N("lr", "ext", "Net extension theorems",
          r"Longo--Rehren Q-systems; Rehren\\"
          r"diagonal construction; M\"uger; DMNO",
          [("App.", "sec:analytic-full-theory")]),
        N("diag", "con", "Diagonal full net theory",
          r"$Z_{\mathrm{diag}}=\sum_i|\chi_i|^2$ from the\\"
          r"A2--A3 sector identification",
          [("Prop.", "prop:analytic-diagonal"),
           ("Eq.", "eq:analytic-diagonal-partition")]),
        N("netext", "con", "Chosen holomorphic net extension",
          r"$\mathcal N_U\subset\mathcal E_3$, index $\mathrm{Dim}\,\mathcal H_3$;\\"
          r"bimodules $\mathcal H_3\boxtimes\mathcal H_3^{\mathrm{op}}$",
          [("Cor.", "cor:analytic-net-extension")]),
        N("tener", "ext", "Annulus and insertion theorems",
          r"Tener: common localizer, module annuli;\\"
          r"Henriques--Tener: transport, insertions",
          [(S, "subsec:analytic-annuli")],
          [(S, "S14.4")]),
        N("dom", "arg", "Dense inverse-energy domains",
          r"round factorization $A_MC_M=\lambda r^{L_0}$",
          [("Lemma", "lem:analytic-inverse-domain")]),
        N("cont", "arg", "Continuation of the insertion form",
          r"identity theorem across the seam;\\"
          r"unique bounded extension",
          [("Lemma", "lem:analytic-insertion-continuation")],
          [(S, "S14.3")]),
        N("a1", "arg", "A1: pairwise annulus comparison",
          r"$\mathcal A^{\mathrm{bl}}_U=\mathcal N_U$; module insertions agree;\\"
          r"a common lift cancels deck phases",
          [("Prop.", "clm:analytic-annulus"),
           ("Eq.", "eq:analytic-annulus-identity")],
          [(S, "S14.2")]),
        N("tfus", "ext", "Fusion-positivity criterion",
          r"Tener: Def.~2.18 and Cor.~4.6",
          [("Thm.", "thm:analytic-complete-unitarity")]),
        N("complete", "con", "Complete VOA unitarity",
          r"positive canonical fusion forms;\\"
          r"strong unitarity is needed first",
          [("Thm.", "thm:analytic-complete-unitarity")]),
        N("gui", "ext", "Unitary Q-systems",
          r"Gui: modules unitarizable;\\unitary relative tensor product",
          [("Lemma", "lem:analytic-unitary-all-modules")]),
        N("allmod", "arg", "All modules over a Q-system",
          r"$\mathcal C_A$, not only local modules,\\is a unitary fusion category",
          [("Lemma", "lem:analytic-unitary-all-modules")]),
        N("voacat", "con", "VOA Haagerup center",
          r"$\mathrm{Rep}(U)\simeq Z(\mathcal H_3)$, unitary ribbon;\\"
          r"original $H/U$: $\mathcal H_2$ or $\mathcal H_3$",
          [("Thm.", "thm:analytic-category")]),
        N("voaext", "ext", "VOA extension theorems",
          r"HKL; Gui; Abe--Buhl--Dong;\\Dong--Mason at $c=8$",
          [("Thm.", "thm:analytic-e8-extension")]),
        N("e8", "con", r"Chosen $H'\cong V_{E_8}$",
          r"all modules $\mathcal H_3$; 36 $U$-preserving\\"
          r"defects $\mathcal H_3\boxtimes\mathcal H_3^{\mathrm{op}}$",
          [("Thm.", "thm:analytic-e8-extension"),
           ("Eq.", "eq:analytic-extension-defects")]),
        N("scope", "open", "Not identified",
          r"$H'$ with the original $H/U$; $\mathcal E_3$ with the\\"
          r"$E_8$ lattice net; whether the reconstruction\\"
          r"functor $\mathcal R$ respects fusion or braiding",
          [("Rem.", "rem:analytic-extension-scope")],
          [(S, "S14.5")]),
    ],
    [
        E("netthm", "subnet"), E("alg", "subnet", label="regularity"),
        E("subnet", "a2a"), E("core", "a2a"), E("alg", "a2a"),
        E("a2a", "a2b"), E("alg", "a2b", label="Lemmas G.1, G.2"),
        E("a2b", "a2c"), E("a2a", "a2c"),
        E("alg", "a2c", label="rank-six argument"),
        E("ht", "a3"), E("core", "a3"),
        E("a2c", "strong"), E("a3", "strong"),
        E("alg", "strong", label="twelve modules"),
        E("a2c", "netH"), E("izumi", "netH"),
        E("netH", "netext"), E("lr", "netext"),
        E("a2c", "diag"), E("a3", "diag"), E("lr", "diag"),
        E("alg", "diag", label="characters"),
        E("a3", "a1"), E("subnet", "a1", label=r"$\mathcal A^{\mathrm{bl}}_U$"),
        E("tener", "a1"), E("dom", "a1"), E("cont", "a1"),
        E("strong", "complete"), E("a1", "complete"), E("tfus", "complete"),
        E("gui", "allmod"),
        E("complete", "voacat"), E("allmod", "voacat"),
        E("izumi", "voacat"),
        E("voacat", "e8"), E("voaext", "e8"),
        E("e8", "scope", style="open"), E("netext", "scope", style="open"),
    ],
    [
        r"A2 and A3 share core methods but are parallel arguments. The net "
        r"route needs no A1; the chosen holomorphic net is not identified "
        r"with $E_8$. The chosen VOA extension $H'$ need not equal the "
        r"original embedding $H/U$. Haagerup categories use all algebra "
        r"modules, not only local modules.",
    ],
    grid={
        "netthm": (0, 0), "subnet": (1.05, 0), "a2a": (2.1, 0),
        "a2b": (3.15, 0), "a2c": (4.2, 0), "netH": (5.3, 0),
        "netext": (6.4, 0),
        "alg": (0, 1.3), "core": (1.1, 1.6), "izumi": (5.3, 1.3),
        "lr": (6.4, 1.3),
        "ht": (0, 2.6), "a3": (2.1, 2.6), "strong": (4.2, 2.1),
        "diag": (6.4, 2.6),
        "tener": (0, 3.9), "a1": (2.1, 4.2), "complete": (3.6, 4.3),
        "voacat": (5.0, 3.7), "scope": (6.95, 3.5),
        "dom": (0, 5.0), "tfus": (2.9, 5.6), "allmod": (5.0, 5.0),
        "e8": (6.2, 4.4),
        "cont": (0, 6.1), "gui": (4.0, 6.2), "voaext": (6.2, 5.7),
    },
    colsep=4.9, rowsep=2.9,
)

# ----- page 7: physics ---------------------------------------------------------

P7 = Page(
    "physics", "From the construction to physical observables",
    r"Sections 2--7: each dataset has explicit mathematical inputs, and the "
    r"two full theories are kept apart.",
    "landscape", 4.7,
    [
        N("fields", "fin", "Actual lattice fields and grades",
          r"mode formula, PCT, norms; $U_2=S_2$;\\"
          r"explicit embedded Potts and parafermion fields",
          [("App.", "sec:construction"), ("Cor.", "cor:initial-grades")],
          [(S, "expdata:coordinates")]),
        N("charthm", "con", "Characters and choice of theory",
          r"twelve $\gamma=0$ characters; diagonal $U$\\"
          r"theory versus the selected $H'\cong V_{E_8}$",
          [("Eq.", "eq:vacuum-character"), ("Eq.", "eq:physics-two-theories")]),
        N("catthm", "con", "Unitary category, full theories",
          r"Haagerup center; canonical $\mathcal H_3$ algebra;\\"
          r"$U$-preserving line interpretation",
          [("Thm.", "thm:analytic-category"),
           ("Thm.", "thm:analytic-e8-extension")]),
        N("recur", "arg", "Exact character recurrence",
          r"$\Xi$ recursion in rational arithmetic;\\"
          r"$E_4/\eta^8=\chi_0+\chi_b+2\chi_a$ checked in every grade",
          [("Eq.", "eq:physics-xi-recurrence"),
           ("Eq.", "eq:physics-e8-character-identity")],
          [(S, "expdata:recurrence")]),
        N("prim", "arg", "Removing Virasoro descendants",
          r"primary multiplicities by convolution",
          [("Eq.", "eq:physics-primary-extraction")]),
        N("spec", "con", "Spin-resolved spectra",
          r"diagonal: gap $2/3$, 2,941 relevant scalars;\\"
          r"$E_8$: scalar gap 2, none relevant; $\Delta\le24$",
          [("Eq.", "eq:physics-relevant-scalars"), (S, "2.4")],
          [(S, "expdata:scalars"), (S, "expdata:spins")]),
        N("tail", "arg", "Tail bound from modular invariance",
          r"the omitted tail is bounded by\\the known spectrum at $b$ and $4\pi^2/b$",
          [("Prop.", "prop:physics-modular-tail")],
          [(S, "S27.3")]),
        N("therm", "con", "Controlled thermal observables",
          r"$Z,F,E,S,C$ with outward-rounded\\intervals and tail certificates",
          [("Eq.", "eq:physics-moment-tail"), (S, "2.5")],
          [(S, "expdata:thermal")]),
        N("corr", "con", "Exact selected correlators",
          r"currents, $u$, Potts and parafermion spin-3\\"
          r"four-point functions; lightest-module blocks",
          [("Eq.", "eq:physics-u-neutral"),
           ("Eq.", "eq:physics-spin3-fourpoint"),
           ("Eq.", "eq:physics-lightest-block")],
          [(S, "expphysics:correlator-details")]),
        N("ward", "arg", "Seeds and Ward completion",
          r"1,137 lattice products, 3,512 projections;\\"
          r"lowering currents complete the tensor",
          [("Eq.", "eq:physics-Ward-completion")]),
        N("tensor", "con", "Complete weight-two chiral tensor",
          r"113 Virasoro primaries;\\18,365 nonzero three-point entries",
          [("Eq.", "eq:physics-primary-three-point"),
           (S, "sec:physics-couplings")],
          [(S, "expphysics:interaction-atlas")]),
        N("modar", "arg", "Exact modular arithmetic",
          r"$S,T$ over $\mathbb Q(\zeta_{13})$; Verlinde fusion;\\"
          r"quantum dimensions",
          [("Eq.", "eq:physics-S"), ("Eq.", "eq:physics-Verlinde")],
          [(S, "S18.1"), (S, "S18.2")]),
        N("defects", "con", "Center defects and Cardy data",
          r"twelve twisted sectors; 78 Cardy annuli;\\boundary $g$ factors",
          [("Eq.", "eq:physics-twisted"), ("Eq.", "eq:physics-Cardy")],
          [(S, "S18.3"), (S, "S18.4")]),
        N("sector", "arg", r"Canonical $\mathcal H_3$ sector assignment",
          r"forgetful multiplicities and adjunction;\\"
          r"tube multiplicity spaces",
          [("Eq.", "eq:physics-forgetful"), ("Eq.", "eq:physics-tube-space")],
          [(S, "S19.1")]),
        N("e8sym", "con", r"Haagerup symmetry of the $E_8$ theory",
          r"invariant scalar gap 2 (1488 or 36 states);\\"
          r"six boundaries, 21 distinct annuli",
          [("Eq.", "eq:physics-H3-scalar-table"),
           ("Eq.", "eq:physics-E8-annuli")],
          [(S, "S19.2")]),
        N("pert", "arg", "Perturbation statements",
          r"dimension-two counts; four abelian\\"
          r"current--current directions",
          [("Eq.", "eq:physics-abelian-deformations")]),
        N("ahkz", "ext", "Published bootstrap plots",
          r"Albert--Honda--Kaidi--Zheng;\\Collier--Lin--Yin",
          [("Fig.", "fig:physics-Haagerup-bootstrap")]),
        N("bootpt", "con", r"Locate the $E_8$ model",
          r"$(c,\Delta)=(8,2)$ below both published\\"
          r"curves; here $c=c_L=c_R=8$",
          [("Eq.", "eq:physics-bootstrap-points")]),
        N("open", "open", "Uncomputed extensions",
          r"nonvacuum bulk sewing; general junctions;\\"
          r"RG endpoints; transported $\mathcal H_3$ off this point",
          [(S, "7.1"), (S, "7.3")]),
    ],
    [
        E("charthm", "recur"), E("recur", "prim"), E("prim", "spec"),
        E("spec", "tail"), E("tail", "therm"), E("spec", "therm"),
        E("fields", "corr"), E("fields", "ward"), E("ward", "tensor"),
        E("charthm", "modar"), E("catthm", "modar"),
        E("modar", "defects"), E("catthm", "defects"),
        E("catthm", "sector"), E("modar", "sector"),
        E("sector", "e8sym"), E("spec", "e8sym", label="scalar gaps"),
        E("spec", "pert"),
        E("e8sym", "bootpt"), E("ahkz", "bootpt"),
        E("corr", "open", style="weak", label="partial input only"),
        E("tensor", "open", style="weak", label="bulk sewing remains"),
        E("pert", "open", style="weak", label="symmetry transport open"),
    ],
    [
        r"The bootstrap point uses $c=c_L=c_R=8$, not $16$. Diagram "
        r"endpoints record what the draft computes; they do not assert a "
        r"complete bulk OPE, a new certified SDP exclusion bound, or a "
        r"symmetry-preserving conformal manifold.",
    ],
    grid={
        "charthm": (0, 0), "recur": (1.15, 0), "prim": (2.3, 0),
        "spec": (3.45, 0), "tail": (4.6, 0), "therm": (5.75, 0),
        "pert": (4.4, 1.3),
        "catthm": (0, 1.8), "modar": (1.2, 1.5), "defects": (2.4, 1.3),
        "sector": (2.4, 2.6), "e8sym": (3.55, 2.6), "bootpt": (5.25, 2.6),
        "ahkz": (6.45, 2.6),
        "fields": (0, 3.9), "corr": (1.2, 3.7), "ward": (1.2, 4.9),
        "tensor": (2.4, 4.9), "open": (4.4, 4.2),
    },
    colsep=4.9, rowsep=3.55,
)

PAGES = [P1, P2, P3, P4, P5, P6, P7]

# ----- final page: concordance of the supplementary appendices ------------

SUPPLEMENT_ROWS = [
    ("S1", "How to audit the inputs", "reading order for the finite inputs", "2--5"),
    ("S2", "The small lattice calculation", "defining field, levels, coefficient field", "2"),
    ("hr:positive-stress-check", "Four-column check of the positive stress identity", "Eq.~104", "3"),
    ("sec:reader-finite", "Finite closure identities a reader can inspect", "minimal generation, Gate~4 residuals, Gate~5 scalars", "2"),
    ("hr:structural-inputs", "Structural inputs for direct checking", "Potts and parafermion rows, membership, core witnesses, irreducibility", "3--4"),
    ("S6", "Reproduction and the remaining large checks", "scope of the small checker and replays", "2--5"),
    ("expfinite:reference", "Expanded finite-lattice reference", "coordinates, generation graph, grade three, 3,970 identities, Gate~4 and Gate~5 records", "2--3"),
    ("expstructure:atlas", "Atlas of the commuting algebras", "lattice--Potts core and its order-13 extension $A_L$", "4"),
    ("expstructure:residual", "Residual conformal vectors", "supplementary; not used by the main argument", "--"),
    ("expstructure:neighbor", "Ambient residual cosets", "supplementary route; not needed for regularity or closure", "--"),
    ("expstructure:tops", "Finite top data behind the energy bound", "universal top bound $h\\le17/10$", "4"),
    ("expstructure:c6", "Charge-six lattice coset", "supplementary route with its own hypotheses", "--"),
    ("expstructure:categorical-diagnostics", "Categorical exclusions: diagnostics", "rank fork, multiplicity six, rank-six check", "4--5"),
    ("expstructure:analytic-map", "Analytic verification map", "A2, A3, A1; the three extension objects", "6"),
    ("expstructure:provenance", "Structural provenance and replays", "replay status of the structural inputs", "3--4"),
    ("expphysics:interaction-atlas", "Weight-two interaction atlas", "complete weight-two chiral tensor", "7"),
    ("expphysics:correlator-details", "Correlator tables and channel expansions", "exact selected correlators", "7"),
    ("expphysics:defect-details", "Modular, fusion and diagonal-defect tables", "modular arithmetic, defects, Cardy data", "7"),
    ("expphysics:extension-details", "Six Haagerup lines and extension boundaries", "$\\mathcal H_3$ sector assignment and $E_8$ symmetry", "7"),
    ("expdata:characters", "Characters through grade 24", "character vector and recurrence", "5, 7"),
    ("expdata:scalars", "Full scalar spectrum", "spin-resolved spectra", "7"),
    ("expdata:spins", "Spin-resolved spectrum", "spin-resolved spectra", "7"),
    ("expdata:thermal", "Thermal intervals and tail certificates", "controlled thermal observables", "7"),
    ("expdata:coordinates", "Coordinate atlas of the small fields", "defining field, Potts and parafermion fields", "2--3, 7"),
    ("expdata:top-atlas", "Finite top witness atlas", "core witnesses; 80-current and 81-top irreducibility", "4"),
    ("sec:review-lean", "Lean formalization: coverage", "abstract steps of Apps.~C, D and G; thermal tail algebra", "2, 4, 7"),
    ("sec:physics-lean-assessment", "Assessment of the physics revision", "scope of each physics dataset", "7"),
    ("exp:assembly", "Source concordance and assembly", "result-to-source map for every page", "all"),
]


# ---------------------------------------------------------------------------
# TeX output
# ---------------------------------------------------------------------------

PREAMBLE = r"""\documentclass[10pt]{article}
%% Generated by hi_cft_c8_dependency_flowchart.py from the labels of
%% c8_expanded_20260929/haagerup_c8_expanded.{aux,toc}. Rerun the script after
%% the expanded draft changes; it rewrites this file.
\usepackage[a3paper,left=15mm,right=15mm,top=22mm,bottom=16mm,
  headheight=12pt,headsep=8mm,footskip=8mm]{geometry}
\usepackage{iftex}
\ifPDFTeX
  \usepackage[T1]{fontenc}
\fi
\usepackage{lmodern}
\usepackage{amsmath,amssymb}
\usepackage[dvipsnames]{xcolor}
\usepackage{array,booktabs,longtable}
\usepackage{fancyhdr}
\usepackage{tikz}
\usetikzlibrary{arrows.meta}
\usepackage[hidelinks,pdfnewwindow=false]{hyperref}
\usepackage{monolith-authorship}
\expandafter\ifx\csname iflatexml\endcsname\relax
  \newif\iflatexml \latexmlfalse
\fi

\hypersetup{pdftitle={Dependency flowchart of the expanded c=8 Haagerup CFT draft},
  pdfauthor={Argument map of the 29 September 2026 expanded draft},
  pdfsubject={Tags link to c8\textunderscore expanded\textunderscore 20260929/haagerup\textunderscore c8\textunderscore expanded.pdf}}

\definecolor{fcink}{HTML}{1F2A44}
\definecolor{fcgrey}{HTML}{6B6F7A}
\definecolor{fcteal}{HTML}{17766F}
\definecolor{finD}{HTML}{C8922A}\definecolor{finF}{HTML}{FFF3D9}
\definecolor{argD}{HTML}{4A76B0}\definecolor{argF}{HTML}{EAF1FA}
\definecolor{conD}{HTML}{3D8A5C}\definecolor{conF}{HTML}{E6F3EA}
\definecolor{extD}{HTML}{85879A}\definecolor{extF}{HTML}{F1F1F4}
\definecolor{optD}{HTML}{8D68AD}\definecolor{optF}{HTML}{F4EEF8}
\definecolor{openD}{HTML}{BE4B48}\definecolor{openF}{HTML}{FBEAEA}
\definecolor{aidD}{HTML}{17766F}\definecolor{aidF}{HTML}{FFFFFF}

\newcommand\fcdraft{c8_expanded_20260929/haagerup_c8_expanded.pdf}
\newcommand\fclink[2]{\href{\fcdraft\##1}{#2}}
\newcommand\fcdot{\,\textperiodcentered\,}
\newcommand\fcsep{\space}
\newcommand\fctype{\fontsize{4.6}{5.6}\selectfont\sffamily\color{fcgrey}}
\newcommand\fctitle{\fontsize{7.2}{8.6}\selectfont\sffamily\bfseries\color{fcink}}
\newcommand\fcbody{\fontsize{6.5}{7.9}\selectfont\sffamily\color{fcink}}
\newcommand\fctag{\fontsize{5.3}{6.4}\selectfont\sffamily\color{fcgrey}}
\newcommand\fcdetail{\fontsize{5.3}{6.4}\selectfont\sffamily\color{fcteal}}
\newcommand\fcedgefont{\fontsize{5.3}{6.2}\selectfont\sffamily\itshape\color{fcgrey}}

\tikzset{
  fc/.style={draw, rounded corners=2.4pt, line width=.55pt, align=flush center,
    inner xsep=3.2pt, inner ysep=2.6pt, text width=#1,
    font=\fontsize{6.5}{8.1}\selectfont\sffamily},
  fin/.style={fc=#1, draw=finD, fill=finF},
  arg/.style={fc=#1, draw=argD, fill=argF},
  con/.style={fc=#1, draw=conD, fill=conF},
  ext/.style={fc=#1, draw=extD, fill=extF},
  opt/.style={fc=#1, draw=optD, fill=optF, dashed},
  open/.style={fc=#1, draw=openD, fill=openF},
  aid/.style={fc=#1, draw=aidD, fill=aidF, densely dotted, line width=.75pt},
  dep/.style={draw=fcgrey!85!black, line width=.5pt,
    -{Stealth[length=4.2pt,width=3.2pt]}},
  thin/.style={draw=fcgrey!70, line width=.35pt,
    -{Stealth[length=3.4pt,width=2.6pt]}},
  optedge/.style={draw=optD, line width=.55pt, dashed,
    -{Stealth[length=4.2pt,width=3.2pt]}},
  openedge/.style={draw=openD, line width=.55pt, dashed,
    -{Stealth[length=4.2pt,width=3.2pt]}},
  weak/.style={draw=openD!80, line width=.55pt, densely dotted,
    -{Stealth[length=4.2pt,width=3.2pt]}},
  aidedge/.style={draw=fcteal, line width=.55pt, densely dotted,
    -{Stealth[length=4.2pt,width=3.2pt]}},
  edgelabel/.style={font=\fcedgefont, fill=white, fill opacity=.85,
    text opacity=1, inner sep=1pt, align=center},
}

\newcommand\fclegendbox[2]{\tikz[baseline=-.6ex]\node[#1=1.9cm, text width=,
  inner xsep=4pt, inner ysep=2pt]{\fontsize{7}{8}\selectfont\sffamily #2};}

\makeatletter
\newcommand\fcsetpage[2]{%
  \setlength\paperwidth{#1}\setlength\paperheight{#2}%
  \ifdefined\pdfpagewidth \setlength\pdfpagewidth{#1}\setlength\pdfpageheight{#2}\fi
  \ifdefined\pagewidth \setlength\pagewidth{#1}\setlength\pageheight{#2}\fi
  \setlength\textwidth{\dimexpr#1-30mm\relax}%
  \setlength\textheight{\dimexpr#2-38mm\relax}%
  \setlength\hsize{\textwidth}\setlength\linewidth{\textwidth}%
  \setlength\columnwidth{\textwidth}\setlength\headwidth{\textwidth}%
  \setlength\vsize{\textheight}\global\@colht\textheight
  \global\@colroom\textheight}
\newcommand\fcportrait{\clearpage\fcsetpage{297mm}{420mm}}
\newcommand\fclandscape{\clearpage\fcsetpage{420mm}{297mm}}
\makeatother

\pagestyle{fancy}
\fancyhf{}
\renewcommand\headrulewidth{0pt}
\fancyhead[L]{\fontsize{7.5}{9}\selectfont\sffamily\color{fcgrey}%
  C=8 HAAGERUP CFT\enspace/\enspace DEPENDENCY FLOWCHART}
\fancyhead[R]{\fontsize{7.5}{9}\selectfont\sffamily\color{fcgrey}%
  Expanded draft of 29 September 2026 (341 pages)\enspace\textperiodcentered\enspace map of 4 October 2026}
\fancyfoot[C]{\fontsize{8}{9}\selectfont\sffamily\color{fcgrey}\thepage}

\newcommand\fcheading[2]{%
  {\fontsize{19}{22}\selectfont\rmfamily\bfseries\color{fcink}#1\par}
  \vspace{2pt}
  {\fontsize{9}{11}\selectfont\rmfamily\color{fcink}#2\par}
  \vspace{5pt}}
\newcommand\fcnotes[1]{\par\vspace{6pt}%
  {\fontsize{8.5}{10.5}\selectfont\rmfamily\color{fcink}#1\par}}
\newcommand\fcstandard{%
  {\fontsize{7.5}{9.5}\selectfont\rmfamily\color{fcgrey}%
  Each tag gives the number and page in
  \href{\fcdraft}{\texttt{c8\_expanded\_20260929/haagerup\_c8\_expanded.pdf}}
  (341 pages) and links to that place; teal lines point to its supplementary
  appendices S1--S28. All construction-dependent conclusions inherit the
  stated finite inputs. This is a map of the draft, not additional proof
  certification.\par}}
\setlength\parindent{0pt}
"""


def legend(kinds):
    boxes = []
    for k in kinds:
        boxes.append(r"\fclegendbox{%s}{%s}" % (k, KINDS[k]))
    return r"\par{" + r"\quad".join(boxes) + r"}\par\vspace{4pt}" + "\n"


def edge_style(e):
    return {"dep": "dep", "thin": "thin", "opt": "optedge",
            "open": "openedge", "weak": "weak", "aid": "aidedge"}[e.style]


def measure(pages, workdir):
    """Typeset every node and return {(page, id): (w, h)} in bp."""
    lines = [PREAMBLE.replace(r"\usepackage{monolith-authorship}", ""),
             r"\begin{document}"]
    for p in pages:
        for n in p.nodes:
            w = f"{p.width_cm}cm"
            lines.append(
                r"\setbox0=\hbox{\begin{tikzpicture}\node[%s=%s] {%s};"
                r"\end{tikzpicture}}" % (n.kind, w, n.content()))
            lines.append(r"\typeout{FCSIZE %s %s \the\wd0\space\the\ht0"
                         r"\space\the\dp0}" % (p.key, n.id))
    lines.append(r"\end{document}")
    path = os.path.join(workdir, "measure.tex")
    open(path, "w").write("\n".join(lines))
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                        "measure.tex"], cwd=workdir, capture_output=True,
                       text=True, errors="replace")
    log = open(os.path.join(workdir, "measure.log"), errors="replace").read()
    if r.returncode != 0:
        sys.stderr.write(log[-4000:])
        raise SystemExit("measurement run failed")
    pending = 0
    overfull = []
    for line in log.split("\n"):
        if line.startswith("Overfull \\hbox"):
            pending += 1
        m = re.match(r"FCSIZE (\S+) (\S+) ", line)
        if m:
            if pending:
                overfull.append(f"{m.group(1)}/{m.group(2)}")
            pending = 0
    if overfull:
        print("overfull node text:", ", ".join(overfull))
    log = log.replace("\n", "")
    sizes = {}
    for m in re.finditer(r"FCSIZE (\S+) (\S+) ([\d.]+)pt\s*([\d.]+)pt\s*([\d.]+)pt",
                         log):
        w = float(m.group(3)) * 72 / 72.27
        h = (float(m.group(4)) + float(m.group(5))) * 72 / 72.27
        sizes[(m.group(1), m.group(2))] = (w, h)
    return sizes


CM = 72 / 2.54


def layout_fixed(page, sizes, workdir):
    """Place nodes on the page's grid and let neato route the edges."""
    rows = max(r for _, r in page.grid.values())
    lines = ["digraph G {", '  splines="true";', '  sep="+5";',
             '  esep="+3";', '  overlap="true";']
    lines.append('  node [shape=box, fixedsize=true, label=""];')
    lines.append('  edge [arrowsize=0.55, fontname="Helvetica", fontsize=6];')
    for n in page.nodes:
        w, h = sizes[(page.key, n.id)]
        c, r = page.grid[n.id]
        x = c * page.colsep * CM
        y = (rows - r) * page.rowsep * CM
        lines.append(f'  "{n.id}" [pos="{x:.1f},{y:.1f}!", '
                     f'width={w / 72:.3f}, height={h / 72:.3f}];')
    for e in page.edges:
        a = []
        if e.label:
            plain = re.sub(r"\$|\\[a-zA-Z]+|[{}^_]", "", e.label)
            a.append('label="%s"' % plain.replace('"', ""))
        lines.append(f'  "{e.a}" -> "{e.b}" [{", ".join(a)}];')
    lines.append("}")
    dot = "\n".join(lines)
    open(os.path.join(workdir, f"{page.key}.gv"), "w").write(dot)
    r = subprocess.run(["neato", "-n2", "-Tjson"], input=dot,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(r.stderr)
    return json.loads(r.stdout)


def layout(page, sizes, workdir):
    if page.grid:
        return layout_fixed(page, sizes, workdir)
    attrs = {"rankdir": "TB", "nodesep": 0.3, "ranksep": 0.4,
             "splines": "spline", "newrank": "true"}
    attrs.update(page.dot_attrs)
    lines = ["digraph G {"]
    for k, v in attrs.items():
        lines.append(f'  {k}="{v}";')
    lines.append('  node [shape=box, fixedsize=true, label=""];')
    lines.append('  edge [arrowsize=0.55, fontname="Helvetica", fontsize=6];')
    for n in page.nodes:
        w, h = sizes[(page.key, n.id)]
        lines.append(f'  "{n.id}" [width={w / 72:.3f}, height={h / 72:.3f}];')
    for e in page.edges:
        a = []
        if e.label:
            plain = re.sub(r"\$|\\[a-zA-Z]+|[{}^_]", "", e.label)
            a.append('label="%s"' % plain.replace('"', ""))
        if not e.constraint:
            a.append("constraint=false")
        if e.weight is not None:
            a.append(f"weight={e.weight}")
        if e.style == "thin":
            a.append("weight=0")
        lines.append(f'  "{e.a}" -> "{e.b}" [{", ".join(a)}];')
    for group in page.ranks:
        lines.append("  { rank=same; " + "; ".join(f'"{g}"' for g in group)
                     + "; }")
    lines.append("}")
    dot = "\n".join(lines)
    open(os.path.join(workdir, f"{page.key}.dot"), "w").write(dot)
    r = subprocess.run(["dot", "-Tjson"], input=dot, capture_output=True,
                       text=True)
    if r.returncode != 0:
        raise SystemExit(r.stderr)
    return json.loads(r.stdout)


def picture(page, g):
    names = {o["_gvid"]: o["name"] for o in g.get("objects", [])}
    bb = [float(x) for x in g["bb"].split(",")]
    out = [r"\begin{tikzpicture}[x=1bp,y=1bp]"]
    out.append(r"\useasboundingbox (%.1f,%.1f) rectangle (%.1f,%.1f);"
               % (bb[0], bb[1], bb[2], bb[3]))
    by_id = {n.id: n for n in page.nodes}
    for o in g.get("objects", []):
        if o["name"] not in by_id or "pos" not in o:
            continue
        n = by_id[o["name"]]
        x, y = (float(v) for v in o["pos"].split(","))
        out.append(r"\node[%s=%scm] (%s) at (%.1f,%.1f) {%s};"
                   % (n.kind, page.width_cm, n.id, x, y, n.content()))
    edges = {(e.a, e.b): e for e in page.edges}
    for ge in g.get("edges", []):
        a, b = names[ge["tail"]], names[ge["head"]]
        e = edges[(a, b)]
        spec = ge["pos"].split()
        end = None
        pts = []
        for tok in spec:
            if tok.startswith("e,"):
                end = tuple(float(v) for v in tok[2:].split(","))
            elif tok.startswith("s,"):
                continue
            else:
                pts.append(tuple(float(v) for v in tok.split(",")))
        path = "(%.1f,%.1f)" % pts[0]
        i = 1
        while i + 2 < len(pts):
            path += " .. controls (%.1f,%.1f) and (%.1f,%.1f) .. (%.1f,%.1f)" % (
                pts[i] + pts[i + 1] + pts[i + 2])
            i += 3
        if end:
            path += " -- (%.1f,%.1f)" % end
        out.append(r"\draw[%s] %s;" % (edge_style(e), path))
        if e.label and "lp" in ge:
            lx, ly = (float(v) for v in ge["lp"].split(","))
            out.append(r"\node[edgelabel] at (%.1f,%.1f) {%s};"
                       % (lx, ly, e.label))
    out.append(r"\end{tikzpicture}")
    return "\n".join(out), (bb[2] - bb[0], bb[3] - bb[1])


def page_tex(page, g):
    pic, (w, h) = picture(page, g)
    kinds = page.kinds or sorted({n.kind for n in page.nodes},
                                 key=list(KINDS).index)
    parts = [r"\fcportrait" if page.orientation == "portrait"
             else r"\fclandscape"]
    parts.append(r"\begin{ai}[Claude]")
    parts.append(r"\fcheading{%s}{%s}" % (page.title, page.subtitle))
    parts.append(r"\iflatexml")
    parts.append(r"\emph{The flowchart on this page is drawn with TikZ and "
                 r"appears in the PDF only.}")
    parts.append(r"\else")
    parts.append(legend(kinds))
    parts.append(r"\begin{center}")
    parts.append(pic)
    parts.append(r"\end{center}")
    parts.append(r"\fi")
    parts.append(r"\fcnotes{%s}" % " ".join(page.notes))
    parts.append(r"\fcstandard")
    parts.append(r"\end{ai}")
    return "\n".join(parts), (w, h)


def concordance_tex():
    rows = []
    for key, title, role, pages in SUPPLEMENT_ROWS:
        num, page, anchor = resolve(key)
        rows.append(r"%s & %s & %s & %s & %s\\" % (
            link(anchor, r"\S\," + num), link(anchor, page), title, role,
            pages))
    return "\n".join([
        r"\fcportrait",
        r"\begin{ai}[Claude]",
        r"\fcheading{Where the supplementary appendices attach}{The "
        r"supplementary appendices S1--S28 print the records behind the "
        r"nodes. Supplementary routes marked ``--'' carry their own "
        r"hypotheses and are not used by the main argument.}",
        r"{\fontsize{9}{11.5}\selectfont\rmfamily",
        r"\begin{longtable}{@{}l r >{\raggedright\arraybackslash}p{.30\linewidth}"
        r" >{\raggedright\arraybackslash}p{.40\linewidth} l@{}}",
        r"\toprule Part & Page & Contents & Used for & Flowchart page\\"
        r"\midrule\endhead",
        r"\bottomrule\endfoot",
        *rows,
        r"\end{longtable}}",
        r"\fcnotes{Appendices A--O keep the numbering of the 78-page base "
        r"revision of 27 September 2026; only their pages moved. The "
        r"verification guide (S1--S6) and the formalization assessment "
        r"(S26--S27) are incorporated companions whose references now "
        r"resolve inside the expanded draft.}",
        r"\fcstandard",
        r"\end{ai}",
    ])


def build_tex(workdir):
    sizes = measure(PAGES, workdir)
    body = []
    report = []
    for p in PAGES:
        g = layout(p, sizes, workdir)
        tex, (w, h) = page_tex(p, g)
        body.append(tex)
        report.append((p.key, p.orientation, w / 72 * 2.54, h / 72 * 2.54))
    body.append(concordance_tex())
    doc = PREAMBLE + "\n\\begin{document}\n" + "\n\n".join(body) \
        + "\n\\end{document}\n"
    return doc, report


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tex-only", action="store_true")
    ap.add_argument("--keep", action="store_true",
                    help="keep the scratch directory")
    args = ap.parse_args()
    os.chdir(HERE)
    LABELS.update(read_aux(f"{DRAFT_DIR}/{DRAFT}.aux"))
    TOC.update(read_toc(f"{DRAFT_DIR}/{DRAFT}.toc"))
    work = tempfile.mkdtemp(prefix="fcbuild-")
    sty_dir = "/home/tzuchen/Codes/monolith/server/src/assets/tex"
    env = dict(os.environ)
    env["TEXINPUTS"] = f"{HERE}//:{sty_dir}//:" + env.get("TEXINPUTS", "")
    try:
        doc, report = build_tex(work)
        for key, orient, w, h in report:
            print(f"{key:12s} {orient:9s} diagram {w:5.1f} x {h:5.1f} cm")
        open(f"{OUT_BASE}.tex", "w").write(doc)
        print(f"wrote {OUT_BASE}.tex")
        if args.tex_only:
            return
        for _ in range(2):
            r = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 f"-output-directory={work}", f"{OUT_BASE}.tex"],
                capture_output=True, text=True, errors="replace", env=env)
            if r.returncode != 0:
                sys.stderr.write(r.stdout[-4000:])
                raise SystemExit("pdflatex failed")
        shutil.copy(os.path.join(work, f"{OUT_BASE}.pdf"), f"{OUT_BASE}.pdf")
        log = open(os.path.join(work, f"{OUT_BASE}.log"),
                   errors="replace").read()
        for w in re.findall(r"^(?:LaTeX|Package) \S* ?Warning.*$", log, re.M):
            print("warning:", w)
        print(f"wrote {OUT_BASE}.pdf")
    finally:
        if args.keep:
            print("scratch:", work)
        else:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
