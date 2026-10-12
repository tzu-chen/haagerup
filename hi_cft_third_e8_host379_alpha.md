# Every simultaneous alpha fixes the host379 commutant

For the actual host379 embedding, every unitary E8 automorphism fixing
the full current algebra

    H=G2_1 tensor A1_4 tensor Heis^2

pointwise fixes its ambient commutant D_E=K(A2,2) pointwise. In particular
this holds for every permitted order-three alpha with E6+A2 fixed algebra,
not only the exhibited representative used to construct the host.
Consequently D_B=Com(H,E8^alpha)=D_E.

## 1. There is no disconnected G2-centralizer component

The standard compact pair G2,F4 in E8 is a full mutual-centralizer pair.
This group-level statement is explicitly given in
[Deligne--Gross, Table1 and the paragraph following it, printed page878](https://www.numdam.org/item/CRMATH_2002__335_11_877_0.pdf).
Its adjoint branching is

    e8=(g2,1) direct sum (1,f4) direct sum (7,26).

One can also remove the possible component-group ambiguity directly.
An element centralizing G2 normalizes the identity component F4 of its
centralizer. F4 has no outer automorphism, so multiply the element by
an F4 element to make it centralize both G2 and F4. The three real
summands displayed above are irreducible and multiplicity-free. The
remaining element acts identically on g2 and f4 and as a real scalar
plus or minus one on (7,26). The minus choice would have fixed Lie
algebra g2 plus f4 of rank six. Every compact E8 automorphism is inner,
and the fixed algebra of an inner automorphism contains a rank-eight
Cartan. Thus the minus choice is impossible. The remaining element is
the identity because E8 is adjoint. This proves the full centralizer is
F4 without invoking the classification of E8 involutions.

## 2. Fixing the two radical currents and the principal A1

Inside F4 use the conformal pair A2_internal,2 times A2_external,1.
The external principal A1_4 is the A1 factor of H. The internal A2
Cartan is precisely the two-dimensional radical of H. The finite
adjoint branching is

    52=(8,1)+(1,8)+(6,3bar)+(6bar,3).

The SU3 representation6 has no zero weight. Hence the centralizer
Lie algebra of the internal Cartan is its two-dimensional torus plus
the external su3. The centralizer of a torus in a connected compact
Lie group is connected; see
[Knapp, Structure Theory of Semisimple Lie Groups, Section3](https://www.math.stonybrook.edu/~aknapp/pdf-files/1-27.pdf).
The full centralizer is therefore the image of T_internal^2 times
SU3_external, possibly divided by a common finite center.

An element in that image which also fixes the external principal SU2
has an SU3_external component commuting with its irreducible
three-dimensional representation. Schur's lemma makes that component
central. A finite central quotient does not change this conclusion:
a lift's commutator with the connected SU2 would take values in a
finite group and is therefore constantly the identity.

Every automorphism fixing H consequently acts as an internal Cartan
element times an external central element. On K(A2_internal,2), the
Cartan action is trivial by the zero-charge commutant definition, and
the external factor is trivial because it commutes with the whole
internal affine VOA. This proves the assertion.

The [ambient branching note](hi_cft_e8_host379_commutant.md) verifies
the conformal pair and its exact commutant. An arbitrary radical
placement in this host is a maximal torus of the internal SU3 and is
conjugate to this one inside the semisimple-current centralizer. The
semisimple embedding is transported from the catalog by the same
inner-conjugacy qualification already used there; it is not the
exceptional simple-A2 linear-equivalence class.

## 3. The residual properness loophole closes for this host

Apply the [rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
with an actual rational radical-lattice completion H inside W.
The trivial possibility D0=D_B is ruled out by the
[ordinary-fixed index-field argument](hi_cft_e8_ordinary_fixed_obstruction.md).
The nontrivial possibility is a proper rank-two action on
D_B=K(A2,2), ruled out by the
[categorical hypergroup obstruction](hi_cft_kA2_hypergroup_obstruction.md).
Thus host379 is excluded under the standing unitary rational
finite-index E8 realization hypotheses, without initially assuming
properness of the restricted operation.

The root agent independently checked the rank argument in Section1.
No numerical computation is used. This concerns the specified E8
fixed-algebra construction and does not identify or exclude the
physical chain's central charge on its own.
