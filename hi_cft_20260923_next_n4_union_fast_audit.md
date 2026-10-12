# Independent audit of the fast N4 union membership checker

23 September 2026. Source review only; no execution by this agent.
The [producer](hi_cft_20260923_next_n4_union_fast.py) passes the following
mathematical, arithmetic and bounded-allocation checks.

The stored normal rows appear in insertion order, followed by the
extra rows. Each was reduced against every earlier pivot. The producer
explicitly asserts zero coefficients at all preceding pivots and unit
coefficient at its own pivot. Thus the forward triangular solve is
correct without requiring the pivot positions themselves to be sorted.
The result is checked on the entire block support, while all target
states outside that support are retained in the residual. In particular
a pivot-only match cannot be mistaken for membership.

All matrix and coefficient arrays use signed int64. Every matrix entry
and solved coefficient lies between0 and p-1. The bound
r*(p-1)^2<2^62, with r<=320 and p=1000003, bounds every dot product,
and the subsequent subtraction also fits int64. No floating arithmetic,
rounding, or probabilistic numerical rank threshold enters elimination.

The selected target list is all ten saved weight-two operators acting
in mode zero on all322 primitive-grade-three basis representatives,
giving3220 targets. Each computed target is checked for grade four and
its expected Cartan weight. Membership is against the fixed6010-row
union, and the source database hash and frozen-source hash chain bind
that union. This is a finite-prime membership statement in those actual
generated words; it does not prove characteristic-zero containment,
an upper dimension bound, or properness.

Each cached dense block is at most320 by4096 int64 entries, about10MiB.
The LRU includes the matrix and conservative lookup allowance in its
64MiB budget. Two bounded state maps, the frozen low-grade inputs,
one target/residual pair, and serialization buffers remain live in
addition. These are consistent with the stated sub-0.6GiB expectation;
the source also stops at a768MiB process-RSS boundary, requires a3GiB
address cap, and uses an alarm covering initialization and arithmetic.
The output database has a64MiB page cap, and no new ambient basis,
large sparse matrix copy, or worker process is created.

Every completed target record and its cursor are committed together.
Timeout or allocation failure rolls back the current transaction,
leaving the prior atomic checkpoint; a subsequent resume checks the
source bindings again. Root alone may launch the producer through the
permanent safe launcher after the sole numerical slot is free.
