# Check the file:line references of Section 5 of TRUST_BOUNDARY.md against the Lean sources:
# for every row, some name of the Lean key must occur on the referenced line(s).
# Usage: python3 lean/tools/trust_boundary/tb_check.py   (after tb_gen.py)
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
C8DIR = os.path.normpath(os.path.join(HERE, '..', '..', 'HaagerupIzumi', 'C8'))
md = open(os.path.join(C8DIR, 'TRUST_BOUNDARY.md')).read()
sec5 = md[md.find('## 5.'):md.find('## 6.')]
# keys whose names are not on the referenced line by construction (conjuncts of a definition,
# instance arguments, Greek/subscripted names)
SKIP = ('certFiniteClosure:', '𝒞 instances', 'hν', 'CharacterInputs.U1', 'UntwistedInputs.h3')
bad = n = 0
for line in sec5.split('\n'):
    if not line.startswith('| ') or line.startswith('| #'):
        continue
    cols = [c.strip() for c in line.split(' | ')]
    if len(cols) < 3:
        continue
    key = re.sub(r'\*.*', '', cols[1]).strip().strip('`')
    m = re.match(r'([A-Za-z0-9/]+\.lean):(\d+)(?:–(\d+))?', cols[2])
    if not m or key.startswith(SKIP):
        continue
    f, a, b = m.group(1), int(m.group(2)), int(m.group(3) or m.group(2))
    path = os.path.join(C8DIR, f)
    if not os.path.exists(path):
        print('NOFILE', f, key)
        bad += 1
        continue
    seg = '\n'.join(open(path).read().split('\n')[a - 1:b])
    body = key.split('.', 1)[1] if '.' in key and not key.startswith('[') else key
    names = [x for x in re.findall(r"[A-Za-z_₀-₉'σμθ]+", body)
             if len(x) > 1 and x not in ('and', 'instances', 'Haar', 'averages', 'arg', 'sub')]
    n += 1
    if not any(x in seg for x in names):
        bad += 1
        print('MISMATCH', key, cols[2], '->', seg[:100].replace('\n', ' / '))
print(n, 'references checked,', bad, 'mismatches')
