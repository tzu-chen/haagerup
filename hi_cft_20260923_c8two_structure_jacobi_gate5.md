# A Jacobi reduction of the remaining weight-five gate

This is a conditional algebraic reduction, not a claim that the outstanding
weight-four or weight-five identities have been checked. It uses the actual
finite spaces and their exact lower-closure certificates. No characteristic-zero
upper bound on the 6,007 selected normal weight-four columns is assumed.

Write

\[
 N_3=K_{-1}S_2+TS_2,\qquad P=S_3/N_3,
\]
\[
 N_4=K_{-1}S_3+TS_3+(S_2)_{-1}S_2,\qquad
 W_4=N_4+P_4,
\]
\[
 N_5=K_{-1}W_4+TW_4+(S_2)_{-1}S_3.
\]

Here these denote the full indicated linear spans, not merely saved independent
subsets. The already certified actual current and Virasoro controls make these
spaces current-stable. Assume Gate 4, namely \((S_2)_0S_3\subset W_4\), including
the neutral-family redundancy. The fixed exact triplet \(P_4\) is a simple
current module of highest weight \((0,2)\). Thus its image
\(Q=W_4/N_4\) is either zero or an isomorphic copy of this triplet.

If \(Q=0\), all the remaining \((S_2)_0P_4\) tests follow immediately from
\((S_2)_0N_4\subset N_5\). Hence the nonzero-triplet case may be used throughout
the reduction without presupposing an upper bound for \(N_4\).

## Two normal-product facts

The zero-mode derivation rule, Gate 4, and the exact lower checks give
\((S_2)_0N_4\subset N_5\). On the first two summands of \(N_4\), this is immediate
from \([a_0,T]=0\) and \(a_0K\subset S_2\). On a product of two weight-two fields,
the only reordered term is \((S_3)_{-1}S_2\); skew symmetry expresses it as
\((S_2)_{-1}S_3\) plus derivatives of the already controlled singular products.

Also
\[
 (N_3)_0S_3\subset N_5.
\]
Indeed, \((Ta)_0=0\), and the normal iterate identity is
\[
 (x_{-1}a)_0p=
 \sum_{i\ge0}x_{-1-i}(a_i p)
 +\sum_{i\ge0}a_{-1-i}(x_i p),
\]
for \(x\in K,a\in S_2,p\in S_3\). The inner vectors have the already controlled
successive grades \(W_4,S_3,S_2,K,\mathbb C\) and
\(S_3,S_2,K,\mathbb C\), respectively. Translation commutators reduce the higher
negative modes to the displayed definition of \(N_5\). This argument does not
assume any \(S_3\)-by-\(S_3\) closure.

## The safe general relation

Let \(B:\Lambda^2(S_2/N_2)\to P\) be the induced zero product, and let
\(\beta:(S_2/N_2)\otimes P\to Q\) be induced by Gate 4. If
\(\sum a_i\wedge b_i\in\ker B\), then, modulo \(N_5\),
\[
 \sum_i \{a_{i,0}\beta(b_i,p)-b_{i,0}\beta(a_i,p)\}=0.
\]
This follows directly from the zero-mode commutator and the two normal-product
facts. It is safe to eliminate the ordered \(P\)-by-\(P\) product this way.
Replacing that ordered product by an exterior square would require additional
control of its positive products and is not used here.

## A particularly small family of relations

The original generator \(u\), operator 7, has highest weight \((1,13)\). The exact
956-dimensional \(S_3\), its exact 634-dimensional \(N_3\), and their homogeneous
echelon rows give the following quotient support bounds:

* \(P\) has no left Cartan weight 2;
* at left Cartan weight 1, its right Cartan weights have absolute value at most 13.

The other seven charged highest fields have weights
\[
 (0,4),(0,8),(0,8),(0,12),(1,1),(1,5),(1,7).
\]
Consequently \(a_0u\in N_3\) for every one of these fields \(a\). This conclusion
uses the exact quotient support; it does not require \(a_0u=0\) in the ambient
VOA.

For \(q=0,2\), take \(p_q\in S_3\) of weight \((-1,q-13)\). Then
\(\beta(a,p_q)=0\) for each of the seven charged fields: for left weight zero,
the output has left weight \(-1\), while for left weight one its right weight
lies outside \(\{-2,0,2\}\). Jacobi therefore gives
\[
 a_0\beta(u,p_q)=0\pmod{N_5}.
\]

An authenticated exact nonzero coefficient of \(P_4\)'s weight-zero vector in
\(u_0p_0\) proves that both its weight-zero and highest vectors satisfy
\(a_0P_4\subset N_5\) for each of these seven \(a\)'s. Raising commutes with
\(u_0\), so the highest case follows as well. In Clebsch--Gordan terms, this
eliminates the highest two channels of each family; the lowest channel remains.
For the family of right highest weight 1, these are its only two channels.

The existing nonzero highest coefficient alone eliminates the highest channel
of each family. A weight-minus-two input for this same highest \(u\) is
unavailable: it would require quotient weight \((-1,-15)\), which is absent.
Thus no conclusion about all three channels follows merely by current raising.

## Precisely identified saved records

The exact H4 record
`A7_zero_r3_000901` in
`hi_cft_20260923_c8two_targeted_h4_trimmed_v2/block_p0_p2.sqlite`
has a nonzero coefficient of column -1, the exact highest \(P_4\) vector:
the stored four field coordinates are
`[-33579/6688, 0, 0, 2289/6688]`.
Its input has weight \((-1,-11)\).

The decisive weight-zero relation is exactly the already requested
`A7_zero_r3_000902`, with input weight \((-1,-13)\), in the final output-weight
\((0,0)\) block. At the time of writing this relation has not been certified.
No new lattice-mode computation is needed to identify which record to inspect.
Before using either coefficient in a final certificate, authenticate its record
digest and complete source graph, and verify the reported exact residual is zero.

The normal-product and quotient arguments above were independently audited by
the c2 agent. This note deliberately leaves numerical coefficient certification
and final channel counts to the root-controlled artifacts.

## Stronger bottom witnesses found in the same closed block

The subsequent read-only record inspection found two already passed bottom
relations in `block_p0_m2.sqlite` of the same closed trim directory:

* `A3_zero_r3_000910`, whose column -3 coefficient has coordinates
  `[-593619,1349829,1399567,-1072149]/9831968`;
* `A6_zero_r3_000899`, whose column -3 coefficient has coordinates
  `[-57967/42018,0,0,22295/798342]`.

Both coefficients are nonzero in the exact biquadratic field. Their input
weights are respectively \((0,-14)\) and \((-1,-9)\). After full source
authentication, they give a more powerful finite reduction: use left witness
field 3 for target families 0,1,2,5,6,7, and witness field 6 for target
families 3,4. In each case the bracket of the two highest fields is normal
because its highest type is absent from \(P\); the exact saved bracket
coordinates may alternatively certify this directly. The bottom input makes
the other \(\beta\) term have weight outside \(Q\). Jacobi therefore kills
the target family's product with the bottom \(P_4\) vector.

Raise this resulting zero identity, using highestness of the target field and
current stability of \(N_5\), to get its other two triplet products. Do not
instead assume the other \(\beta\) term vanishes for every raised input: for
families 1 and 2 with witness 3, the twice-raised input can have nonzero
\(\beta\). The bottom identity alone suffices.

This clears every charged family, conditional on Gate 4 and the authenticated
two records. The neutral family follows if charged-pair zero products span
\(P\): expand the neutral-to-charged bracket in such products, then use
Jacobi twice and the already completed charged families. The new bounded
producer `hi_cft_20260923_c8two_structure_charged_span.py` tests precisely
that positive spanning statement by a lowering-coinvariant certificate in
the independently exact 322-dimensional quotient. Its success, rather than
any unsupported rank upper bound for normal products, is the required
additional input.
