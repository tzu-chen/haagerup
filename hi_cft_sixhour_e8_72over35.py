"""Exact retained-chiral scalar residues for an E8 proper-current coset.

No linear algebra or numerical solver. Coordinate even this tiny checker
with the sole numerical slot and run through the 128 MiB safe-run guard.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def main():
    # K(A2,2)=SU2_1^3/SU2_3. Use the field identification to fix
    # the first level-one label to zero, then impose center parity.
    parafermion = []
    for a in (0, 1):
        for b in (0, 1):
            for ell in range(4):
                if (a+b+ell) % 2 == 0:
                    h = (F(a+b, 4)-F(ell*(ell+2), 20)) % 1
                    parafermion.append({"level_one_labels": [0, a, b],
                                        "level_three_label": ell, "h_mod1": str(h)})
    assert len(parafermion) == 8
    multiplicities = {str(h): sum(F(r["h_mod1"]) == h for r in parafermion)
                      for h in {F(r["h_mod1"]) for r in parafermion}}
    assert multiplicities == {"0": 1, "1/2": 3, "1/10": 3, "3/5": 1}
    virasoro, seen = [], set()
    for r in range(1, 6):
        for s in range(1, 7):
            key = min((r, s), (6-r, 7-s))
            if key in seen:
                continue
            seen.add(key)
            h = F((7*r-6*s)**2-1, 168)
            virasoro.append({"r": r, "s": s, "h": str(h),
                             "h_mod1": str(h % 1)})
    assert len(virasoro) == 15
    residues = sorted({(F(p["h_mod1"])+F(v["h_mod1"])) % 1
                       for p in parafermion for v in virasoro})
    scalar = sorted(2*h for h in residues)
    intervals = {"phi": (F(2, 21), F(16, 105)),
                 "epsilon": (F(33, 140), F(2, 7))}
    for lo, hi in intervals.values():
        assert lo in scalar and hi in scalar
        assert not any(lo < x < hi for x in scalar)
    result = {
        "central_charge": "72/35",
        "parafermion_coset_labels": parafermion,
        "minimal_model_labels": virasoro,
        "chiral_twist_residues": list(map(str, residues)),
        "necessary_scalar_residues_in_0_to_2": list(map(str, scalar)),
        "forbidden_open_scalar_intervals": {
            name: list(map(str, limits)) for name, limits in intervals.items()},
        "scope": "Necessary residue superset for all local scalar fields in any full CFT retaining K(A2,2) x Vir M(6,7) on both chiral halves. Includes every local chiral extension. Not every listed residue must occur as a scalar, and the finite-chain estimates are not assumed exact continuum dimensions.",
    }
    path = Path("hi_cft_sixhour_e8_72over35_results.json")
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"central_charge": result["central_charge"],
          "forbidden_intervals": result["forbidden_open_scalar_intervals"],
          "output": str(path)}), flush=True)


if __name__ == "__main__":
    main()
