# Finite Zhu actions: an explicit obstruction and a usable cutoff

23 September 2026. Read-only algebra and primary-source audit; no numerical
job was launched. The present U is strongly rational, c=8, vertex generated
in weights one and two, and all its simple modules have 0<=h<=17/10.

## What the matrix construction does and does not imply

Huang's A^N(V) and the Dong--Li--Mason A_N(V) are different algebras.
The former has off-diagonal matrix entries; the latter is recovered as a
special diagonal subalgebra. In
[Huang, Theorems 4.2, 4.6 and 5.13](https://arxiv.org/html/2009.00262v4),
finite dimensionality of A^N uses finite spanning representatives of
V/C_(k+l+2)(V) for 0<=k,l<=N. The module comparison theorem uses the
complete A^N action. It gives no assertion that arbitrary weak vertex
generators, restricted to the finite strip, generate this action.
The global difference bound 17/10 permits N=2 in that theorem, not N=1.

There are three distinct quantities: the lowest weights of modules, the
weights of fields needed to span the matrix algebra, and the intermediate
grades of seed-mode words constructing those fields. A bound for the first
does not in these results bound the other two. Moreover Huang's Gr uses
the Omega filtration defined by all V fields; it cannot be replaced without
proof by an easily computed filtration using only the seed fields.

## A rational c=8 counterexample to weak generation of A^1

Let L=Z alpha with (alpha,alpha)=4, and put

    V = V_L tensor V_E7.

Take as weak generators e^alpha, e^(-alpha), omega_L, all of weight two,
together with a basis of the E7 currents, of weight one. They generate V:
the lattice vertex formula gives

    (e^alpha)_2 e^(-alpha) = epsilon(alpha,-alpha) alpha(-1)1,

and the current alpha(-1)1 together with e^alpha,e^(-alpha) generates V_L.
Positive-definite even lattice VOAs are rational and C2-cofinite, with
simple modules indexed by dual-lattice cosets; see
[Zhu, Section 6](https://www.ams.org/journals/jams/1996-9-01/S0894-0347-96-00182-8/S0894-0347-96-00182-8.pdf)
and [Dong--Li--Mason, regularity](https://arxiv.org/abs/q-alg/9508018).

The four V_L lowest weights are 0,1/8,1/2,1/8. The two E7 lowest
weights are 0,3/4. Thus V has c=8, a unique weight-zero simple, and
every simple has lowest weight at most 5/4<17/10.

Consider its vacuum levels V_0 direct_sum V_1. Its first factor has only
1 in grade zero and alpha(-1)1 in grade one. Every mode of either
e^alpha or e^(-alpha) whose source and target stay in these two grades
vanishes, since a state of either nonzero lattice charge has weight at
least two. The lattice Virasoro modes preserve the two lines separately:
L(-1)1=0 and L(1)alpha(-1)1=0. E7 currents act only in the second factor.
Therefore all products of the compressed seed operators preserve

    C alpha(-1)1 tensor 1

and its complement in V_0 direct_sum V_1. But the actual A^1(V) action
contains the matrix entry of alpha(-1)1 from grade zero to grade one,
namely alpha(-1), sending 1 to alpha(-1)1. The compressed seed algebra
is strictly smaller than the complete A^1(V) image.

This is a VOA counterexample, not only a counterexample for a generic
graded associative algebra. It refutes the proposed implication even
with rationality, c=8, generator weights at most two, and the stronger
top bound h<=5/4. It does not assert that no larger cutoff can work for
this example; in fact the missing current is already a word passing
through lattice grade two.

## The same weak seeds do not generate any DLM A_n

The top lines of V_(L+alpha/4) and V_(L-alpha/4) both have weight 1/8.
On both, the zero modes of e^alpha and e^(-alpha) vanish, while omega_L
acts by 1/8. Tensoring the E7 vacuum, every listed seed has the same
top action on these two different simple modules. In contrast,
alpha(0) acts by +1 and -1. Hence their classes cannot generate A_0(V).
Because A_n(V) maps onto A_0(V), the zero-mode classes of these weak
seeds cannot generate any DLM A_n(V), including A_1(V).
The higher-Zhu generation results of
[Addabbo--Barron](https://arxiv.org/html/2110.07671)
require additional spanning or structural hypotheses; they do not remove
this obstruction for arbitrary weak generators.

## A genuine explicit field-weight cutoff once a C2 cutoff is certified

Suppose a finite homogeneous space X represents V/C2(V), with every
nonvacuum element of X of weight at most D. The difference-one spanning
theorem of
[Gaberdiel--Neitzke](https://arxiv.org/html/hep-th/0009235)
gives words

    x1(-n1) ... xr(-nr)1,  n1>...>nr>0,  xi in X.

Modulo C_p(V), every word with n1>=p vanishes: its leftmost mode is
obtained from a -p mode by differentiating its field. Thus representatives
can be chosen with r<=p-1 and all ni in {1,...,p-1}. Their weights obey

    wt <= (p-1)D + (p-1)(p-2)/2.

Applying the weight-lowering reduction in Huang's finite-dimensionality
proof to these explicit representatives yields the sufficient cutoff

    A^N(V) is spanned by [v]_(k,l), wt(v)<=(2N+1)(D+N).

In particular, 3D+3 suffices for A^1, and 5D+10 for A^2. The same
largest cutoff covers the diagonal DLM subalgebra. This is a sufficient
bound and is not claimed optimal.

To use it for U one must certify X+C2(U)=U; bare C2-cofiniteness only
asserts some finite X exists. Nor can D be replaced by two merely because
U has weak generators of weights one and two. Finally the field-weight
cutoff does not provide a seed-word excursion bound: exact membership
and formulas for the required fields still have to be supplied.
