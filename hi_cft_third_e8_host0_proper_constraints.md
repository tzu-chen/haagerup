# Proper host0 actions force a nontrivial alpha action and a rootless full lattice

The proper-action version of the abelian six-current E8 route has
stronger constraints than the initial lattice example suggested.
The intrinsic alpha action must be nontrivial on the ambient
rank-two lattice commutant. Moreover, the full orthogonal
rank-six lattice VOA must already lie in the fixed algebra and
must be rootless. These are necessary conditions, not an existence
or continuum-identification theorem.

## 1. Setup and the categorical input

Let
\[
 E=V_{E_8},\qquad W\subset B=E^\alpha,\qquad
 [E:B]=3,\quad [B:W]=I=2+3d,\quad
 d=(3+\sqrt{13})/2.
\]
Assume the finite-index unitary fixed-algebra setup, including the
compatible conditional expectation, of the
[c=1 host report](hi_cft_third_e8_c1_hosts.md).
Here \(W_1\) is the six-dimensional abelian algebra, and the
rank-two quotient restricted to its commutant is **proper**.

Put
\[
 L=E_8\cap\mathfrak z^\perp,\quad K=E_8\cap\mathfrak z,
 \quad q=\det L=\det K,\quad D_E=V_L.
\]
The actual radical lattice \(M\subset K\) gives \(V_M\subset W\);
write \(n=[K:M]\).

After an inner conjugation preserving the six-current torus, alpha
is toral. Thus
\[
 D_B=D_E^\alpha=V_{L_B},\qquad
 e=[L:L_B]\in\{1,3\},\qquad
 |\operatorname{Rep}D_B|=e^2q.                       \tag{1}
\]
This does not require alpha to fix lattice ground states of \(K\)
at this stage.

The [stabilizer-nine argument](hi_cft_third_e8_pointed_hosts.md)
can be strengthened: the fusion category of a proper pointed
rank-two quotient contains a near-group subcategory
\(\operatorname{NG}(H,9)\), with \(|H|=9\).
Its pointed central metric on \(H\) is nondegenerate, and the
full fusion category factors as
\[
 \mathcal C\simeq\operatorname{NG}(H,9)\boxtimes\mathcal P,
 \qquad |\mathcal P|=\frac{e^2q}{9}.                 \tag{2}
\]
The precise proof and primary-source scope are in the independently
audited [near-group factorization](hi_cft_third_pointed_neargroup_factorization.md).
The needed all-category input is
[Izumi, Theorem9.1 and Lemma7.4](https://maths.anu.edu.au/files/8%2520Izumi_2.pdf).
It removes the extra \(H^2\)-triviality assumption in the earlier
Cuntz presentation. The pointed half-braidings and center
dimensions also appear in
[Evans–Gannon, Section4.3](https://arxiv.org/abs/1208.1500).

In particular the modular category of \(D_0=\operatorname{Com}(W_1,W)\)
has a pointed factor with the underlying fusion category
\(\mathcal P\) (its braiding reversal depends on the incoming-center
convention), and its other simple objects
have dimensions
\[
 1+3d,\qquad 2+3d,\qquad 3d.                         \tag{3}
\]
Its only rational-dimensional simples are its \(|\mathcal P|\)
invertibles. This does not identify the other modular factor with
the untwisted Haagerup center in every case: \(H=C_9\) also occurs,
and twisted Haagerup-type centers must not be silently discarded.

## 2. Ambient branching forces e=3

Let \(T=V_M\otimes D_0\). Index multiplicativity gives
\[
 \operatorname{qdim}_T E=neqI,\qquad
 \operatorname{qdim}_T W=\frac{neq}{3}.              \tag{4}
\]
The second number is rational. Because every dimension in (3)
has a positive coefficient of \(d\), every constituent of \(W/T\)
must be pointed.

There is a useful general multiplicity fact. If \(A\) is the
connected algebra for \(D_0\subset D_B\), an invertible \(g\) of
\(D_0\) has simple free induction:
\[
 \operatorname{End}_A(g\otimes A)=\operatorname{Hom}(1,A)
 =\mathbb C,\qquad
 \operatorname{qdim}_A(g\otimes A)=1.
\]
If \(g\) occurs in an ordinary local \(D_B\)-module, reciprocity
identifies that module with its free induction. The occurrence is
unique and has multiplicity one. No unproved locality of arbitrary
free inductions is used.

The unimodular primitive-lattice branching gives exactly \(n\)
\(V_M\) branches per \(D_E\)-module. Restriction \(D_E\to D_B\)
splits each into \(e\) distinct ordinary modules, so each appearing
\(D_B\)-module still has \(n\) such branches. Consequently the entire
pointed \(T\)-part of \(E\) has dimension at most
\[
 n|\mathcal P|=\frac{ne^2q}{9}.                      \tag{5}
\]
Combining (4) and (5) yields
\[
 \frac{neq}{3}\leq\frac{ne^2q}{9}
 \quad\Longrightarrow\quad e\geq3.
\]
Since \(e\in\{1,3\}\),
\[
 \boxed{e=3,\qquad D_B\ne D_E.}                      \tag{6}
\]
This explains why the
[first explicit determinant72 example](hi_cft_third_e8_host0_candidate.md),
whose alpha action on \(D_E\) was trivial, cannot give a compatible
proper-action realization.

## 3. Saturation fixes the full orthogonal lattice

For \(e=3\), equations (4) and (5) are equalities. Thus \(W\) must
contain the entire pointed \(T\)-part of \(E\).

Every \(V_M\)-module arising from \(V_K\) is accompanied by the
\(D_B\) vacuum, whose restriction contains the \(D_0\) vacuum.
These are pointed \(T\)-constituents. Saturation therefore gives
\[
 \boxed{V_K\subset W.}                              \tag{7}
\]
It follows that the actual fixed radical lattice is all of \(K\),
so \(M=K\) and \(n=1\). Since the full \(W_1\) is six-dimensional,
\(K\) has no norm-two vectors. Also \(K\subset B\), because
\(V_K\subset W\subset B\).

This is stronger than merely finding a rootless finite-index
sublattice of \(K\). A rootful \(K\) cannot be repaired by passing
to a rootless \(M\) in this proper-action setting.

For example, a primitive ambient \(L=\operatorname{diag}(2,4)\)
can realize \(L_B=\operatorname{diag}(6,12)\) with nontrivial alpha.
Take
\[
 u=(1,-1,0,0,0,0,0,0),\quad
 t=(1,1,1,1,0,0,0,0),\quad h=u+t.
\]
Then \(u^2=2,t^2=4,u\cdot t=0\), and alpha is represented by \(h/3\).
Its fixed-root count is46 integer roots plus32 half-integer roots,
giving the required \(E_6+A_2\) fixed Lie dimension86.
The kernel lattice is generated by \(u+t,2u-t\), with norms6,12.
However its orthogonal \(K\) has roots, so (7) excludes this
small determinant rescue as well.

## 4. A larger, rootless constructive family

One can instead choose a primitive rank-two plane containing
a norm-six representative \(h\) of the order-three action.
For such an \(h\),
\[
 h^\perp\cap E_8=Q(E_6)\oplus Q(A_1).
\]
Choose a second lattice vector \(k\) whose projection \(r\)
onto this rank-seven complement is regular: its pairing with
every root is nonzero. Then
\(K=h^\perp\cap k^\perp\cap E_8\) is rootless.

After Weyl conjugation, every Dynkin coefficient of \(r\) is a
positive integer. Thus
\[
 r=\rho_{E_6}+\rho_{A_1}+\lambda,\qquad
 \lambda\ \text{dominant},\qquad
 \rho_{E_6}^2+\rho_{A_1}^2=78+\tfrac12.
\]
To obtain \(3\nmid q=\det\langle h,k\rangle\), the \(E_6\)
discriminant component of \(r\) must be nonzero. The smallest
increase is a minuscule \(\omega_1\) or \(\omega_6\):
\[
 2(\rho,\omega_1)+\omega_1^2
 =16+\tfrac43=\tfrac{52}{3}.
\]
Therefore this short-representative family satisfies
\[
 q=6r^2\geq575.                                    \tag{8}
\]
This is **not a universal bound on host0**: (7) supplies a
cocharacter in the rank-two plane, but it does not guarantee
that a globally shortest norm-six representative remains in
that plane.

There is an exact abstract candidate attaining (8):
\[
 r=\rho_{E_6}+\omega_1+\rho_{A_1},\qquad
 k=r+h/6.
\]
The discriminant norm is \(2/3+1/4+1/12=1\), so one can choose
the E8 glue orientation with \(k\in E_8\). Then
\[
 h^2=6,\quad h\cdot k=1,\quad k^2=96,\qquad
 \operatorname{Gram}\langle h,k\rangle=
 \begin{pmatrix}6&1\\1&96\end{pmatrix},\quad\det=575. \tag{9}
\]
The pair is primitive: \(h\) is primitive, and an unshifted simple
root \(\beta\) perpendicular to \(h\) has \(k\cdot\beta=1\);
unimodularity then provides a unit pairing minor.
Regularity of \(r\) excludes every root from its orthogonal \(K\).
The coordinate and glue certificate has now passed all28 checks
under the root agent's128MiB guarded launcher (about20MiB RSS):
[source](hi_cft_third_e8_host0_det575_check.py),
[exact results](hi_cft_third_e8_host0_det575_results.json).
It finds the explicit vectors
\[
 h=(2,0,1,1,0,0,0,0),\qquad
 k=(5,4,-4,-5,3,2,1,0).                            \tag{10}
\]
The certificate verifies actual E8 membership, the unit pairing
minor, the primitive complement, the order-three \(E_6+A_2\)
fixed-root system, and
\[
 \operatorname{Gram}L_B=
 \begin{pmatrix}6&3\\3&864\end{pmatrix},
 \qquad\det L_B=5175.
\]
It also finds an explicit integral basis of \(K\).

Streaming the complete E8 shells through norm8 gives
\[
 \#K_2=0,\qquad\#K_4=28,\qquad\#K_6=50,\qquad\#K_8=76.
\]
The ambient shell totals240,2160,6720,17520 provide independent
enumeration controls. Hence the \(V_K\) vacuum coefficients
through grade4 are
\[
 (1,6,55,316,1447),
\]
and the necessary \(V_K\otimes\operatorname{Vir}_{c=2}\) lower
coefficients are
\[
 (1,6,56,323,1510).
\]
The proposed \(\Gamma_0\) Haagerup fixed character has grade2,3
coefficients120 and956, so both necessary inequalities pass.
The character comparison does not fix the remaining branching
or construct \(D_0\).

Even after that certificate, the essential missing object remains
an actual proper fixed subalgebra \(D_0\subset V_{L_B}\).
The categorical dimensions, a rootless \(K\), and a compatible
pointed local extension do not themselves construct its
operator products or identify the chain's continuum theory.
