#!/usr/bin/env python3
"""Compose tb_linemap.json with the line changes between a snapshot of the ProofMap sources and
the current sources: python3 tb_rebase.py <snapshot dir> FILE.lean ...

For each FILE, the map old-line -> snapshot-line (identity if FILE is not yet in the map) is
composed with snapshot-line -> current-line (difflib on the two versions)."""
import difflib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
C8 = os.path.normpath(os.path.join(HERE, '..', '..', 'HaagerupIzumi', 'C8'))
snap = sys.argv[1]
path = os.path.join(HERE, 'tb_linemap.json')
M = json.load(open(path))
for f in sys.argv[2:]:
    ol = open(os.path.join(snap, f)).read().split('\n')
    nl = open(os.path.join(C8, f)).read().split('\n')
    sm = difflib.SequenceMatcher(None, ol, nl, autojunk=False)
    step = {}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        for k in range(i2 - i1):
            step[i1 + k + 1] = (j1 + k + 1) if tag == 'equal' else (j1 + min(k, max(j2 - j1 - 1, 0)) + 1)
    old = M.get(f) or {str(i): i for i in range(1, len(ol) + 1)}
    M[f] = {k: step.get(v, v) for k, v in old.items()}
    print(f, 'shifts', sorted(set(v - int(k) for k, v in M[f].items()))[:12])
json.dump(M, open(path, 'w'))
