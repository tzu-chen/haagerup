# Exact-two current denominators: ambient currents versus fixed currents

The [proper-current catalog](hi_cft_sixhour_e8_proper_current_results.json)
has42 rows with Sugawara denominator charge six.
[Their complete host witnesses](hi_cft_sixhour_e8_c2_current_rows.json)
are extracted directly from the saved exact output. A row is
an embedding class and abelian rank, not a CFT.

| E8 database row | Semisimple denominator | Added abelian rank |
|---:|---|---:|
| 0 | zero | 6 |
| 1 | \(A_{1,1}\) | 5 |
| 4,5 | \(A_{1,4}\), distinct embeddings | 4 |
| 70 | \(A_{2,1}\) | 4 |
| 72,74 | \(A_{2,3}\), distinct embeddings | 2 |
| 86 | \(B_{2,2}\) | 2 |
| 93 | \(A_{1,1}^2\) | 4 |
| 97 | \(A_{1,1}A_{1,4}\) | 3 |
| 137,138 | \(A_{1,2}^2\), distinct embeddings | 3 |
| 146 | \(A_{1,2}A_{1,10}\) | 2 |
| 197 | \(A_{1,4}^2\) | 2 |
| 282 | \(A_{1,1}A_{2,1}\) | 3 |
| 285 | \(A_{1,4}A_{2,1}\) | 2 |
| 305 | \(A_{1,3}A_{2,2}\) | 1 |
| 340 | \(A_{1,2}B_{2,1}\) | 2 |
| 358 | \(A_{1,1}B_{2,2}\) | 1 |
| 360 | \(A_{1,4}B_{2,2}\) | 0 |
| 372 | \(A_{3,1}\) | 3 |
| 401 | \(A_{1,1}^2A_{2,1}\) | 2 |
| 404 | \(A_{1,1}A_{1,4}A_{2,1}\) | 1 |
| 411 | \(A_{1,2}^2A_{2,1}\) | 1 |
| 419 | \(A_{1,4}^2A_{2,1}\) | 0 |
| 426 | \(A_{1,1}A_{1,3}A_{2,2}\) | 0 |
| 467 | \(A_{1,2}A_{1,4}B_{2,1}\) | 0 |
| 483 | \(A_{2,1}^2\) | 2 |
| 496 | \(A_{1,4}A_{3,1}\) | 1 |
| 514 | \(A_{2,1}B_{2,2}\) | 0 |
| 579 | \(A_{1,1}^3A_{2,1}\) | 1 |
| 613 | \(A_{1,4}A_{2,1}^2\) | 0 |
| 887 | \(A_{1,1}^3\) | 3 |
| 892 | \(A_{1,1}^2A_{1,4}\) | 2 |
| 915 | \(A_{1,1}A_{1,2}^2\) | 2 |
| 959 | \(A_{1,1}A_{1,4}^2\) | 1 |
| 991 | \(A_{1,2}^2A_{1,4}\) | 1 |
| 1018 | \(A_{1,2}A_{1,4}A_{1,10}\) | 0 |
| 1045 | \(A_{1,4}^3\) | 0 |
| 1058 | \(A_{1,1}^4\) | 2 |
| 1064 | \(A_{1,1}^3A_{1,4}\) | 1 |
| 1150 | \(A_{1,1}^4A_{1,4}\) | 0 |

The possible full fixed-current hosts are:

| Host row | Full current algebra | Sugawara charge |
|---:|---|---:|
| 0 | \(U(1)^6\) | 6 |
| 372 | \(A_{3,1}U(1)^4\) | 7 |
| 379 | \(A_{1,4}G_{2,1}U(1)^2\) | \(34/5\) |
| 483 | \(A_{2,1}^2U(1)^3\) | 7 |
| 496 | \(A_{1,4}A_{3,1}U(1)\) | 6 |
| 514 | \(A_{2,1}B_{2,2}U(1)\) | 7 |
| 579 | \(A_{1,1}^3A_{2,1}U(1)^2\) | 7 |
| 600 | \(A_{1,1}^2A_{1,4}B_{2,1}\) | \(13/2\) |
| 613 | \(A_{1,4}A_{2,1}^2\) | 6 |
| 617 | \(A_{1,3}A_{2,1}A_{2,2}\) | 7 |

## Three false positives of the coarse host-rank test

Rows72 and74 have only host617. An \(A_{2,3}\) inside
\(A_{1,3}\oplus A_{2,1}\oplus A_{2,2}\) must project trivially
to \(A_1\), and diagonally, up to automorphisms, onto both
\(A_2\) factors: their induced levels one and two must add to
three. Its centralizer in the host is exactly the remaining
\(A_{1,3}\), of rank one. It cannot supply two commuting
abelian currents. Both host witnesses are therefore impossible.

Row5 has hosts579 and617. In host579, an \(A_{1,4}\) is either
principal in the \(A_{2,1}\), or diagonal in the three
\(A_{1,1}\) factors and a regular \(A_{1,1}\subset A_{2,1}\).
These exhaust level four because an \(A_1\) in \(A_2\) has
index one or four. The principal possibility is the distinct
E8 row4: its centralizer is \(E_6\). The diagonal possibility
has only the regular \(A_2\) centralizer \(U(1)\) and the host's
two abelian currents, hence centralizer rank three. That is
insufficient for the four extra abelian currents required by
row5.

In host617, level four requires either the principal
\(A_{1,4}\subset A_{2,1}\), or the diagonal of \(A_{1,3}\)
and a regular \(A_{1,1}\subset A_{2,1}\). The internal
\(A_{2,2}\) has \(A_1\) levels two or eight and cannot supply
any other combination summing to four. In either case the
host centralizer has rank three, again insufficient.
Thus row5 is also impossible.

This leaves39 necessary denominator rows. The reduction uses
actual simultaneous containment, which was deliberately not
claimed by the earlier graph-and-total-rank superset.

## A structural consequence for the ambient commutant

Let \(K=Z_{\mathfrak e_8}(A_{\rm ss})\), with rank \(R_K\),
and let \(H_r\subset K\) be the added abelian currents. Then
\[
 \operatorname{Com}(A_{\rm ss}\oplus H_r,E_8)_1
   =Z_K(H_r)\cap H_r^\perp
\]
has rank \(R_K-r\). Centralizers of tori retain the full rank,
and orthogonal subtraction removes the \(r\) central directions.

The exact centralizer certificates show \(R_K>r\) for every
one of the42 rows except5 and72. For the four cases whose
stored rank certificate is only a bound, the recorded
centralizer dimensions suffice: dimension45 cannot have rank
at most three; dimension28 cannot have rank at most two;
dimension7 cannot have rank at most one. These cover rows138,
146,340,411 respectively. Thus the only possible current-free
ambient cases were5 and72, both removed above.

**Every remaining actual ambient current commutant at exact
\(c=2\) in this audited class has nonzero weight one.**
This is a current-algebra statement; it does not assume a
particular full-CFT modular invariant.

## Why this is not yet the chain's neutral-current exclusion

Ambient currents need not be fixed by the noninvertible
Haagerup action. The physical premise presently used is
absence of jointly Haagerup- and shift-invariant currents.
The algebra relevant to that test is
\(\operatorname{Com}(A,W)_1\), not automatically the full
ambient weight-one space.

There is a useful exact split by host. For hosts of Sugawara
charge \(6,13/2,34/5\), the relative current coset
\(\operatorname{Com}(A,\langle W_1\rangle)\) has charge
\(0,1/2,4/5\). It cannot contain a nonzero unitary current,
since any such current already requires Sugawara charge at
least one. Therefore every actual denominator in these host
branches has no Haagerup-invariant current at weight one.
The no-current premise alone does not exclude them.

For hosts of charge seven, that relative coset has charge one.
Its weight-one algebra can be zero, \(U(1)\), or \(A_{1,1}\).
In either nonzero case its real dimension is odd, so an
order-three shift fixes a current. Such host placements are
conditionally excluded. Zero weight one is possible: two
independent diagonal \(A_{1,2}\) subtractions in four
\(A_{1,1}\) factors leave an Ising-times-Ising relative coset
of charge one. Thus a general charge-seven exclusion would
be incorrect; the embedding-specific relative coset is needed.

The same distinction applies to inherited \(\alpha\): a
compatible order-three E8 action fixes \(W_1\) by construction,
but it need not fix every ambient current, and an action
trivial on a vacuum VOA can still act on full-CFT modules.
No fixed-VOA or full-CFT identification is inferred here.
