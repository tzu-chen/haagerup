# Recognition of cyclic HI from a specified Lagrangian algebra

Research note, 7 September 2026. This is a **conditional theorem**, not
an existence construction. Neither the required modular tensor category
nor the algebra in the theorem has been constructed uniformly here.

The arithmetic and matrix conventions are those of Section 105 of
[the main notes](haagerup_izumi_class_field_stark_notes.md).
Put \(n\geq3\) odd, \(D=n^2+4\), and \(d=(n+\sqrt D)/2\).
Use the finite quadratic modules

\[
 A=(\mathbb Z/n)^2,\quad q_A(x,y)=xy/n,\qquad
 \Gamma=\mathbb Z/D,\quad q_\Gamma(u)=-n(2^{-1}\bmod D)u^2/D.
\]

Label the modular matrices (105.10) by
\[
 0,\ \pi,\ g_{(x,y)}\ ((x,y)\ne0\text{ modulo simultaneous negation}),
 \quad \gamma_u\ (u\ne0\text{ modulo negation}).
\]
The corresponding dimensions are \(1,d^2,1+d^2,d^2-1\);
all these central labels are self-dual. Let
\[
 \Lambda=\mathbf1\oplus\pi\oplus
       \bigoplus_{x=1}^{(n-1)/2}2g_{(x,0)}.
 \tag{1}
\]

**Theorem.** Suppose a unitary modular tensor category \(\mathcal B\)
realizes these labeled \(S,T\), and suppose (1) admits an actual
connected commutative separable unitary algebra structure. Then
\(\mathcal C=\mathcal B_\Lambda\) is a unitary cyclic Haagerup–Izumi
fusion category. Its pointed subcategory is untwisted. In particular,
no separate assumption about the simple objects, cyclic action, or
fusion rules of its module category is necessary.

The assumption is about a multiplication satisfying the categorical
algebra axioms. The vector in (1), its dimension, and its invariance
under \(S,T\) do not establish that assumption.

## 1. The rank and the full adjunction Gram matrix

Write \(\mathcal D=n(1+d^2)=1/S_{00}\). Equation (105.13) gives
\(\dim(\Lambda)=\mathcal D=\sqrt{\dim(\mathcal B)}\), so the
assumed algebra is Lagrangian. The central lift of the free-module
functor \(F:\mathcal B\to\mathcal C\) is an equivalence
\(\mathcal B\simeq Z(\mathcal C)\), and the right adjoint \(I\) of \(F\) satisfies
\(I(\mathbf1)=\Lambda\). Also \(\dim(\mathcal C)=\mathcal D\).
This is the Lagrangian reconstruction of
[Davydov–Müger–Nikshych–Ostrik, Corollary 4.1 and Proposition 4.4](https://arxiv.org/pdf/1009.2117).

The usual underlying-object formula for central induction gives
\[
 FI(X)=\bigoplus_{Y\in\operatorname{Irr}(\mathcal C)}YXY^*.
 \tag{2}
\]
At \(X=\mathbf1\), adjunction therefore gives
\[
 |\operatorname{Irr}(\mathcal C)|
 =\dim\operatorname{End}_{\mathcal B}(\Lambda)
 =1+1+4(n-1)/2=2n.
 \tag{3}
\]
This equality does not assume the HI rank in advance.

Let \(\langle\, ,\,\rangle\) denote the ordinary inner product on
Grothendieck groups in which simples are orthonormal. If \(v\) is
the multiplicity vector (1), the Gram matrix of the \(F(i)\) is
\[
 M_{ij}=\langle F(i),F(j)\rangle
 =\langle i,j\Lambda\rangle
 =\sum_k S_{ik}S_{jk}\frac{v_k}{S_{0k}}.
 \tag{4}
\]
Here Verlinde and \(Sv=v\) give the last equality. All \(S_{0k}>0\),
so
\[
 \operatorname{rank}M=\operatorname{rank}F_*=(n+3)/2.
 \tag{5}
\]
In (5), \(F_*\) is the complexified Grothendieck-group map.

For \(g=g_{(x,y)}\), \(h=g_{(x',z)}\), (4) evaluates to the following
complete table, with the symmetric entries understood:

| \(i,j\) | \(M_{ij}\) |
|---|---:|
| \(0,0\) | \(1\) |
| \(0,\pi\) | \(1\) |
| \(0,g\) | \(2\delta_{y,0}\) |
| \(0,\gamma\) | \(0\) |
| \(\pi,\pi\) | \(n+1\) |
| \(\pi,g\) | \(n+2\delta_{y,0}\) |
| \(\pi,\gamma\) | \(n\) |
| \(g,h\) | \(n+2\delta_{y,z}+2\delta_{y,-z}\) |
| \(g,\gamma\) | \(n\) |
| \(\gamma,\gamma'\) | \(n\) |

For clarity, this evaluation uses only the \(0,\pi\), and
\((t,0)\) columns. With \(a=1/n,b=1/\sqrt D\), their nonzero
eigenvalues in (4) are \(2/(a-b),2/(a+b),2n\).
The sum of the first two is \(nD\). The remaining terms reduce by
\[
 \sum_{t\bmod n}\cos(2\pi yt/n)\cos(2\pi zt/n)
       =\frac n2(\delta_{y,z}+\delta_{y,-z}).
\]
For example the \(g,h\) entry is
\[
 a^2(nD)+8na^2\sum_{t=1}^{(n-1)/2}
       \cos(2\pi yt/n)\cos(2\pi zt/n)
 =n+2\delta_{y,z}+2\delta_{y,-z}.
\]

## 2. Positivity forces all simple dimensions

The last entry of the table shows that all the actual objects
\(F(\gamma)\) have the same class. Denote it by \(R\). Then
\[
 \langle R,R\rangle=n,\qquad \dim R=nd,\qquad
 \langle R,\mathbf1\rangle=0,\qquad F(\pi)=\mathbf1+R.
 \tag{6}
\]
The equality of two actual classes follows because the squared
norm of their difference is zero.

Initially define the **virtual integral** classes
\[
 K_y=F(g_{(x,y)})-R.
 \tag{7}
\]
The table proves that (7) depends only on \(y\) up to sign, that
\(K_0=2\mathbf1\), and, for one representative of each nonzero
pair \(y,-y\), that
\[
 \langle K_y,K_z\rangle=2\delta_{[y],[z]},\qquad
 \langle K_y,R\rangle=\langle K_y,\mathbf1\rangle=0,\qquad
 \dim K_y=2.
 \tag{8}
\]
It would be premature to assume that these differences are objects.

Let \(\mathbf f\) be the vector of positive simple dimensions of
\(\mathcal C\), and let \(\mathbf m\) be the nonnegative integral
multiplicity vector of \(R\). Set
\(\mathbf a=\mathbf e_1+\sum_{[y]\ne0}K_y\), an integral vector.
The orthogonal projection of \(\mathbf f\) onto
\(\operatorname{span}\{\mathbf1,K_y,R\}\) is
\(\mathbf a+d\mathbf m\). Its squared norm is
\[
 1+\frac{n-1}{2}\frac{2^2}{2}+\frac{(nd)^2}{n}
 =n(1+d^2)=\|\mathbf f\|^2.
\]
Consequently
\[
 \mathbf f=\mathbf a+d\mathbf m,\qquad
 \|\mathbf a\|^2=\|\mathbf m\|^2=n,\qquad
 \langle\mathbf a,\mathbf m\rangle=0.
 \tag{9}
\]

By (3), there are \(2n\) coordinates. Since \(\mathbf m\) is
nonnegative integral and has squared norm \(n\), at least \(n\)
coordinates have \(m_X=0\). At each such coordinate,
\(f_X=a_X\) is a positive integer. These coordinates already
contribute at least \(n\) to \(\|\mathbf a\|^2=n\).
Equality forces exactly \(n\) zeros of \(\mathbf m\), with
\(a_X=1\) there and \(a_X=0\) elsewhere. The other \(n\)
coordinates have \(m_X=1\).

Thus \(\mathcal C\) has exactly \(n\) invertible simples of
dimension 1 and \(n\) noninvertible simples of dimension \(d\);
\(R\) is the sum of the latter, each once. Moreover
\(\langle K_y,\mathbf a\rangle=2\) and \(\|K_y\|^2=2\).
Integrality forces each \(K_y\) to be the sum of two distinct
invertibles, with positive coefficients. Equation (8) says these
pairs are disjoint and cover all the nonidentity invertibles.

## 3. The invertibles form the cyclic group of order n

The image of \(F_*\) is a central subalgebra of \(K_0(\mathcal C)_\mathbb C\).
Its kernel, by (4), is the span of the primitive idempotents with
\(v_k=0\). Therefore its character coordinates are precisely
the \(0,\pi,(t,0)\) columns with \(v_k>0\).

In these coordinates \(K_y\) evaluates to 2 at \(0,\pi\), and
to \(2\cos(2\pi yt/n)\) at \((t,0)\). It follows that
\[
 K_yK_z=K_{y+z}+K_{y-z},\qquad K_0=2\mathbf1.
 \tag{10}
\]
This equality follows in the image algebra, so it is also an
equality of its integral classes in \(K_0(\mathcal C)\).

Each \(K_y\) is self-dual since all the central labels are
self-dual. The invertible group has odd order \(n\), and a
nonidentity self-dual invertible would have order 2. Thus
\(K_1=\alpha+\alpha^{-1}\) for some invertible \(\alpha\).
The recurrence from (10) gives
\[
 K_y=\alpha^y+\alpha^{-y}\quad\text{for all }y.
 \tag{11}
\]
Their supports cover every nonidentity invertible. Therefore
\(\alpha\) generates the entire group, and has order \(n\).

## 4. Inversion covariance and every noninvertible product are forced

For any two noninvertible simples \(X,Y\), the dimension of
\(XY^*\) is \(d^2=1+nd\). All simple dimensions are 1 or \(d\),
and \(d\) is irrational. Comparing the rational and irrational
parts shows that \(XY^*\) contains exactly one invertible
summand, counting multiplicity. Frobenius reciprocity says that
there is exactly one invertible \(a\) with \(aY\cong X\).
The left action is therefore free and transitive.

Choose a noninvertible \(\rho\). For some residue \(r\),
\(\rho\alpha\cong\alpha^r\rho\). Centrality of
\(K_1=\alpha+\alpha^{-1}\), and freeness of the left action,
give \(r=1\) or \(r=-1\).

The first possibility would make the whole Grothendieck ring
commutative, since it is generated by \(\alpha,\rho\). But in a
commutative fusion ring, (2) says that \(F_*I_*\) is multiplication
by
\[
 c=\sum_Y YY^*.
\]
On the left regular representation, multiplication by \(c\) is
\(\sum_Y N_YN_Y^*\), a positive definite matrix: the \(Y=\mathbf1\)
term is the identity. It is invertible. Thus \(F_*\) would be
surjective onto a vector space of dimension \(2n\), contradicting
(5). This excludes \(r=1\) and proves
\[
 \rho\alpha=\alpha^{-1}\rho.
 \tag{12}
\]

Write \(\rho^*=\alpha^k\rho\). Applying duality twice and (12)
gives \(\rho=\alpha^{2k}\rho\), whence \(k=0\) by oddness and
freeness. Thus \(\rho\) is self-dual. Conjugation by \(\alpha^a\)
sends \(\rho\) to \(\alpha^{2a}\rho\) and fixes \(\rho^2\).
It acts transitively on all noninvertibles. The multiplicities
of these objects in \(\rho^2\) must therefore be equal.
Self-duality supplies one unit, and dimension forces the common
noninvertible multiplicity to be 1:
\[
 \rho^2=\mathbf1+\sum_{g\bmod n}\alpha^g\rho.
 \tag{13}
\]
Equations (12)–(13), together with \(\alpha^n=\mathbf1\),
are all the cyclic HI fusion rules.

## 5. The pointed associator is untwisted

The branching already proved gives, by adjunction,
\[
 I(\alpha)=\bigoplus_{x\bmod n}g_{(x,1)}.
 \tag{14}
\]
These \(n\) distinct central labels have twists \(e^{2\pi ix/n}\)
and dimension \(1+d^2\). The central-induction indicator formula
therefore gives
\[
 \nu_n(\alpha)=
 \frac{\operatorname{Tr}(\theta_{I(\alpha)}^n)}{\dim\mathcal C}
 =\frac{n(1+d^2)}{n(1+d^2)}=1.
 \tag{15}
\]
We use the positive spherical structure of the unitary category.
The formula is
[Ng–Schauenburg, Theorem 4.1](https://arxiv.org/pdf/math/0601012).

The pointed subcategory has the form
\(\operatorname{Vec}_{\mathbb Z_n}^{\omega}\).
For the class \(k\in H^3(\mathbb Z_n,\mathbb C^\times)\cong\mathbb Z_n\),
its generator has \(n\)-th indicator \(e^{2\pi ik/n}\), in the
standard cocycle convention. This is computed in
[Ng–Schauenburg, Section 9, preceding Lemma 9.3](https://arxiv.org/pdf/math/0601012).
Indicators agree in the full pointed subcategory and in
\(\mathcal C\), so (15) forces \(k=0\). This completes the theorem.

## 6. Remaining existence problem and checks

The theorem removes the fusion-rule identification step from the
modular route in Section 105: an actual unitary realization of
its modular matrices together with the specified Lagrangian algebra
already suffices for cyclic HI, for every odd \(n\geq3\).
It does not construct either input, prove that the invariant vector
admits multiplication, or imply C from the analytic phase identities.
Existence for infinitely many orders is still unresolved.

The proof is uniform and uses no finite census. As a check of the
explicit arithmetic feeding it,
[the small verifier](hi_pell_metric_groups.py) independently builds
(4) from \(S,v\) and compares every entry with the Gram matrix of
the derived branching at \(n=3,5,7,9\). The
[saved results](hi_pell_metric_groups_results.txt) also cover the
quadratic-module calculations of Section 105. These finite checks
do not construct a fusion category or an algebra object.
