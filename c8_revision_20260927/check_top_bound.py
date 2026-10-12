"""Independent rational reconstruction of the manuscript's fourteen core tops.

Run only through hi_cft_safe_run.py, coordinated by the root agent.
Estimated peak: < 64 MiB; time: < 1 second; no third-party modules or workers.
This checks arithmetic from the printed charge formulas. It does not certify
the VOA embedding, the spectral field witness, or the highest-space argument.
"""

from fractions import Fraction as F
import json


def balanced13(n):
    return (n + 6) % 13 - 6


def potts(flag, charge):
    if flag == "x":
        return F(0) if charge % 3 == 0 else F(2, 3)
    return F(2, 5) if charge % 3 == 0 else F(1, 15)


# label, true core weight, top dimension, 4680 times stress trace, |j| minima.
EXPECTED = (
    ("x0", "0", 1, 0, (0,)),
    ("x1", "2/15", 1, 600, (0,)),
    ("x2", "2/5", 5, 10440, (0, 3)),
    ("x3", "4/5", 9, 56640, (0, 2, 3, 6)),
    ("x4", "1/3", 2, 5520, (6,)),
    ("x5", "1", 14, 148560, (1, 4, 6)),
    ("x6", "4/5", 6, 54240, (4,)),
    ("y0", "2/5", 1, 7800, (0,)),
    ("y1", "8/15", 7, 36960, (0, 5)),
    ("y2", "4/5", 15, 110880, (0, 2, 3, 5)),
    ("y3", "1/5", 2, 4080, (2,)),
    ("y4", "11/15", 14, 81480, (1, 2, 4, 6)),
    ("y5", "2/5", 6, 18240, (1, 4)),
    ("y6", "1/5", 2, 4920, (4,)),
)


def reconstruct(flag, a):
    # Enumerate all states by actual Cartan charge, independently of the
    # older two-stage T-top then extension-orbit implementation.
    states = []
    for charge in range(-12, 13):
        j = balanced13(charge)
        k = balanced13(-5 * j)
        left = F(charge % 2, 4)
        p = potts(flag, charge)
        z = F(a * (a + 1), 15) - F(k * k, 13) + max(0, abs(k) - a)
        assert z >= 0
        h = F(charge * charge, 156) + left + p + z
        states.append((h, charge, j, left, p, z))
    h = min(state[0] for state in states)
    minima = [state for state in states if state[0] == h]
    dim = 0
    left_trace = F(0)
    cartan_square = F(0)
    potts_trace = F(0)
    pf_trace = F(0)
    character = {}
    for _, charge, _, left, p, z in minima:
        multiplicity = 1 + charge % 2
        character[charge] = character.get(charge, 0) + multiplicity
        dim += multiplicity
        left_trace += multiplicity * left
        cartan_square += multiplicity * charge * charge
        potts_trace += multiplicity * p
        pf_trace += multiplicity * z
    for charge, multiplicity in character.items():
        assert character[-charge] == multiplicity
    w = (left_trace + F(83, 6084) * cartan_square
         + F(25, 6) * potts_trace + F(25, 26) * pf_trace)
    assert h * dim == left_trace + cartan_square / 156 + potts_trace + pf_trace
    assert w == (left_trace / 26 + F(7, 936) * cartan_square
                 + F(125, 39) * potts_trace + F(25, 26) * h * dim)
    return {
        "label": flag + str(a), "h": h, "dimension": dim,
        "L": left_trace, "Q": cartan_square, "P": potts_trace,
        "Z": pf_trace, "4680W": 4680 * w,
        "absolute_j_minima": tuple(sorted({abs(state[2]) for state in minima})),
        "right_charge_character": character,
    }


def main():
    # Printed cutoff argument: the balanced representatives give every
    # T-top at weight <= 14/13; charges outside [-12,12] cost more alone.
    for flag in ("x", "y"):
        for j in range(-6, 7):
            assert F(j*j, 156) + F(j % 2, 4) + potts(flag, j) <= F(14, 13)
    assert F(13*13, 156) > F(14, 13)
    rows = [reconstruct(flag, a) for flag in ("x", "y") for a in range(7)]
    for row, expected in zip(rows, EXPECTED, strict=True):
        label, h, dim, trace, minima = expected
        assert (row["label"], row["h"], row["dimension"], row["4680W"],
                row["absolute_j_minima"]) == (label, F(h), dim, trace, minima)

    inequality_1 = [row["right_charge_character"].get(10, 0)
                    - row["right_charge_character"].get(12, 0) for row in rows]
    inequality_2 = [F(row["right_charge_character"].get(7, 0)
                      - row["right_charge_character"].get(9, 0), 2) for row in rows]
    assert inequality_1 == [0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0]
    assert inequality_2 == [0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1, 0, 0]
    residual = [7956, 7356, 29340, 14964, 10392, 0, 22212,
                156, 18732, 0, 11832, 1188, 29496, 10992]
    for row, c1, c2, remainder in zip(rows, inequality_1, inequality_2, residual, strict=True):
        assert remainder >= 0
        assert (4680 * F(17, 10) * row["dimension"] - row["4680W"]
                == 8460 * c1 + 28716 * c2 + remainder)
    result = {
        "status": "pass", "exact_arithmetic": "fractions.Fraction",
        "rows_checked": len(rows), "universal_top_bound": "17/10",
        "checks": ["cutoff", "all minima", "dimensions", "stress traces",
                   "charge characters", "two sl2 inequalities", "dual identity"],
        "rows": rows,
        "scope": "Printed arithmetic only; no embedded VOA or field identity is inferred.",
    }
    print(json.dumps(result, default=str, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
