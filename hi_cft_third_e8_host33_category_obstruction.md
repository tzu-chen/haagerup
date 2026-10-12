# A proper Haagerup quotient is impossible for the rational principal D5 coset category

The [later modular trace obstruction](hi_cft_third_flavoured_universal_obstruction.md)
excludes the corresponding current host without coset rationality.
This note preserves the separate categorical theorem and its original
rationality qualification; that qualification is not needed by the
new direct exclusion.

Let S be the modular category of the local order-two simple-current
extension of SU2_60, and let P be any pointed category with group C4.
There is no unitary fusion category with a full central inclusion
S tensor P and the proper two-element Haagerup quotient of weight d²,
where d=(3+sqrt(13))/2. This is a categorical statement. Applying it to
the actual principal D5_1/SU2_60 coset still requires the rationality
and finite-frame hypotheses recorded in the
[host33 follow-up](hi_cft_third_e8_host33_followup.md).

## 1. The exact SO3 module-category input

Use theta=pi/62 and [n]=sin(n theta)/sin(theta). In
[Evans--Pugh, Theorem5.12](https://arxiv.org/pdf/1804.07714), S is
SO(3)_30, namely m=15 in their SO(3)_(2m) notation. It is the local
SU2_(4m) extension, not the full even subcategory before condensation.
The theorem classifies unitary *-module categories, which is exactly
the needed scope. There are only two indecomposable types:

    regular A30: [1],[3],...,[29],[31]/2,[31]/2  (rank17);
    sigma30:     [2],[4],...,[30]                (rank15).

These are the even and odd halves of D32; see their Table1 and
Figure5. Their regular Perron vector is stated in the proof of
Theorem5.5, and the odd vector follows from the same D32 Perron
vector. Both vectors here have squared norm

    D=Dim(S)=31/(4 sin(theta)^2).                         (1)

For the odd vector, sum sin²(j pi/31) for j=1,...,15 equals31/4.
For the regular vector, the fifteen odd terms below31 give29/4;
the two half-sized split vertices add1/2, giving31/4 as well.
Thus no relative normalization is left implicit.

## 2. Pointed action and the scale of the nontrivial component

Suppose such a fusion category C exists. The proper quotient gives

    C=B direct sum M,    B=S tensor P,
    Dim(M)=d² Dim(B)=4d²D.

M is indecomposable as a B-module. This is the central double-coset
decomposition supplied by
[Bischoff, Theorem5.16](https://arxiv.org/pdf/1608.00253), with the
neutral-dimension fraction derived explicitly in Section1 of the
[K(A2,2) obstruction](hi_cft_kA2_hypergroup_obstruction.md).
It is not an ordinary C2 grading.

Restrict M to S. The invertible C4 objects act by S-module
autoequivalences and transitively permute its indecomposable summands.
All summands therefore have the same one of the two types in Section1.
Their number r divides4; put h=4/r in {1,2,4}. Their Perron scales
are equal because invertibles preserve dimension. Equation(1) gives

    dim_M(simple i)=sqrt(h) d p_i,                       (2)

where p_i is the corresponding displayed Perron entry. This uses only
the restriction as module categories, not a tensor factorization of C.

## 3. Field separation eliminates sigma30 and regular h=2

Let F=Q(2cos(pi/31)), a totally real degree15 field. Every regular
Perron entry is in F, and the odd-vector entries have the form

    [2j]=[2] r_j,    r_j in F,   r_j>0,
    a=[2]^2=2+2cos(pi/31) in F.

The exact norm is N_(F/Q)(a)=31. For example, with z primitive of
order62 and x=z+z^(-1), Phi_62(z)=z^15 Psi_62(x), evaluation at z=-1
gives that norm from Phi_62(-1)=31.

F has odd degree, so sqrt(13) is not in F. For any h=1,2,4, neither
h a nor h a/13 is a square in F: their rational norms respectively
are h^15 times31 and h^15 times31/13^15, neither a rational square.
The elementary quadratic-extension criterion then says

    sqrt(h a) not in F(sqrt(13)).                         (3)

In the sigma case every M dimension is sqrt(h a) d times a positive
element of F. A product of two M dimensions belongs to F(sqrt(13)).
Every B dimension belongs to F. Comparing the two field components
in any product of two M simples therefore forces its M part to vanish.
But its total dimension has a nonzero d coefficient, because d²=1+3d,
so it cannot be the dimension of B objects alone. Contradiction.

For the regular type h=2, use sqrt(2) in place of sqrt(h a). Neither
2 nor2/13 is a square in F, as their norms are2^15 and2^15/13^15.
The identical product-dimension argument excludes this case.

Only the regular type with h=1 or4 remains.

## 4. Low-dimensional products close an actual pointed quotient

The regular S-module has a unique dimension-one node, its vacuum.
Call the corresponding least-dimension M simple X. Its dimension is
sqrt(h)d. The C4 action permutes these least nodes transitively, with
stabilizer of order h. Since every nonvacuum S object takes the
regular vacuum node to a nonvacuum node, reciprocity gives

    pi_B(XX*)=direct sum_(g in stabilizer) g.

More generally the B part of a product of any two least M objects
contains only pointed C4 objects. Its dimension is h by the proper
quotient's neutral fraction. The M part consequently has dimension
3h d. After dividing by sqrt(h)d, it is a nonnegative integer sum
of regular S dimensions equal to

    3sqrt(h)=3 or6.                                    (4)

Only the S dimensions 1,[3],[5] can be at most6. Indeed the unsplit
ones increase up to[29], [7]>6, and the split dimension
[31]/2=1/(2sin(theta))>6. These inequalities can be verified without
floating-point arithmetic: sin(7theta)/sin(theta) is at least
7-343theta²/6>6 using theta<22/(7*62), and 1/(2theta)>6.
With x=2cos(pi/31),

    [3]=1+x,    [5]=x²+x-1.

Since x has degree15, the three values 1,[3],[5] are rationally
independent. Equation(4) can therefore contain only dimension-one
terms. Thus the M part of every product of least objects also
contains only least objects.

The four invertibles together with these least M objects form a
closed, duality-stable full fusion subcategory. Centrality restricts
to it, and the same neutral fraction and nontrivial quotient weight
d² remain. It is therefore an actual pointed Haagerup quotient over
C4. The [stabilizer-nine theorem](hi_cft_third_e8_pointed_hosts.md),
proved from formal codegrees, requires an order-nine stabilizer in
C4. This is impossible.

All cases have now been excluded. The proof does not assume that the
original S tensor P inclusion splits the ambient fusion category,
and it does not assume a classification of arbitrary nonunitary
module categories.

## 5. Exact consequence and unresolved VOA input

If the principal coset C is strongly rational with the finite-frame
bridge, its [normal-pair calculation](hi_cft_third_e8_host33_followup.md)
identifies Rep(C) with (Rep(U') tensor Rep(A3_1))^rev, so the theorem
applies. The universal restriction lemma then leaves only a trivial
residual or a proper one. The latter is excluded here. The trivial
case is separately excluded by the same dimension-field index
argument when the frame is rational: all H and C dimensions lie
in the cyclotomic field of conductor dividing248, which does not
contain sqrt(13), whereas [E8:W]=3I does.

This is a conditional categorical completion, not an independent
proof of C2-cofiniteness or rationality of the principal coset. The
finite-index VOA/net bridge must be supplied before changing an
unqualified host33 catalog status. The simultaneous-alpha domain is
now fixed uniformly by Section2 of the host33 follow-up. The complete
module-category and field argument was independently read and checked
by the integrability agent, including both Perron normalizations and
the closed least-object subcategory. No numerical computation is used.
