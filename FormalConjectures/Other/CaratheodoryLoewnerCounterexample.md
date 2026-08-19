# Proof of the smooth Carathéodory–Loewner counterexample

This note is a formalisation-oriented reconstruction of the counterexample announced by
Levent Alpöge on 19 August 2026:

- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203).

The post says that, with

\[
 f(x+iy)=-\frac14\cos(2x)+\frac3{10}\cos(2y)-\frac1{32}\cos(4y)
          +\sin x\sin y,
\]

and, for a positive integer \(k\),

\[
 g_k(z)=10^{10}+\frac{|z|^2}{1+|z|^2}
 \exp\!\left(-|z|^{-1/4}e^{-|z|^2}\right)
 f\!\left(\left(\frac{100}{\bar z}\right)^{k/2}\right),                 \tag{1}
\]

the origin is an umbilic of index \(1+k/2\), and \(g_2\), regarded as a smooth function
on \(S^2=\mathbb P^1(\mathbb C)\), is the support function of a convex body with exactly
one umbilic.

The circulated writeup mentioned in the post is not public at the time of writing. Everything
below is therefore derived directly from (1). The proof is arranged as a sequence of lemmas that
can be translated to Lean without changing the mathematical decomposition.

## 1. Conventions and the exact theorem

Write \(z=x+iy\), \(r=|z|\), and

\[
 E(r)=\exp\!\left(-r^{-1/4}e^{-r^2}\right),\qquad
 A(r)=\frac{r^2}{1+r^2}E(r).
\]

At \(z=0\), the nonconstant term in (1) is defined to be zero. Thus \(g_k(0)=10^{10}\).

For a real \(C^2\) function \(u\) on a plane, put

\[
 q_{\mathrm E}(u)=u_{xx}-u_{yy}+2i u_{xy}=4u_{\bar z\bar z}.             \tag{2}
\]

At an isolated zero of (2), our principal-line index is half the winding number of
\(q_{\mathrm E}(u)\) on a small positively oriented circle. This is the convention used by
`HasIsolatedZeroIndex` in the Lean statement.

On the round sphere, use stereographic coordinates in which

\[
 ds^2=\lambda(z)^2|dz|^2,\qquad \lambda(z)=\frac2{1+|z|^2}.
\]

The \((0,2)\)-part of the covariant Hessian is

\[
 Q_z(u)=u_{\bar z\bar z}+\frac{2z}{1+|z|^2}u_{\bar z}.                  \tag{3}
\]

It vanishes exactly when the trace-free spherical Hessian vanishes. Its winding number is twice
the index of the corresponding principal line field. Multiplication of (3) by a positive scalar
does not affect its zeros or winding number.

We prove the following more explicit result.

**Theorem.**

1. Every \(g_k\) is \(C^\infty\) at the origin.
2. If \(k>0\), the origin is an isolated zero of both the Euclidean operator (2) and the
   spherical operator (3), and both have winding number \(k+2\) there.
3. The function \(g_2\) extends smoothly to \(S^2\).
4. The spherical operator (3) for \(g_2\) has no zero away from the origin.
5. The tensor \(\nabla^2 g_2+g_2g_{S^2}\) is positive definite. Consequently \(g_2\) is the
   support function of a smooth strictly convex body, whose unique umbilic is the point \(z=0\).

## 2. The seed function has no umbilics

The important feature of \(f\) is that its trace-free Hessian is uniformly separated from zero.
Direct differentiation gives

\[
\begin{aligned}
 4f_{\bar w\bar w}
 &= f_{xx}-f_{yy}+2if_{xy}\\
 &=\cos(2x)+\frac65\cos(2y)-\frac12\cos(4y)
      +2i\cos x\cos y.                                                  \tag{4}
\end{aligned}
\]

Put \(u=\cos x\), \(v=\cos y\), \(s=u^2\), and \(t=v^2\). Then

\[
 \operatorname{Re}(4f_{\bar w\bar w})
 =2s+\frac{32}{5}t-4t^2-\frac{27}{10},qquad
 |\operatorname{Im}(4f_{\bar w\bar w})|^2=4st.                         \tag{5}
\]

The following exact bound is the central finite certificate:

\[
             |4f_{\bar w\bar w}|\ge \frac7{50}.                        \tag{6}
\]

Here is an elementary verification suitable for `nlinarith`. For fixed \(t\), the square of
the left side of (6) is the convex quadratic

\[
 P_t(s)=\left(2s-4t^2+\frac{32}{5}t-\frac{27}{10}\right)^2+4st.
\]

Its unconstrained minimum occurs at

\[
 s_*(t)=\frac{4t^2-(37/5)t+27/10}{2}.
\]

Split \(0\le t\le1\) into the following three rational intervals.

- If \(0\le t\le1/10\), then \(s_*(t)\ge1\), so the minimum on \([0,1]\) occurs at
  \(s=1\). Write
  \[
  A_1(t)=-4t^2+\frac{32}{5}t-\frac7{10},
  \qquad P_t(1)=A_1(t)^2+4t.
  \]
  If \(t\ge1/64\), then \(P_t(1)\ge4t\ge1/16\). If \(t\le1/64\), then
  \(A_1(t)\le1/10-7/10=-3/5\), so \(P_t(1)\ge9/25\). Thus in either case
  \(P_t(1)\ge1/16>(7/50)^2\).
- If \(1/10\le t\le1/2\), substitute \(s=s_*(t)\). The result is
  \[
  t\left(8t^2-\frac{69}{5}t+\frac{27}{5}\right)\ge\frac14.
  \]
  For a rational certificate, subtract \(1/4\) and factor:
  \[
  \left(t-\frac12\right)
  \left(8t^2-\frac{49}{5}t+\frac12\right).
  \]
  Both factors are nonpositive on this interval. For the second one, subtract its value
  \(-2/5\) at \(t=1/10\) and factor the difference as
  \[
  \left(t-\frac1{10}\right)
  \left(8\left(t+\frac1{10}\right)-\frac{49}{5}\right)\le0.
  \]
- If \(1/2\le t\le1\), then \(s_*(t)\le0\), so the minimum occurs at \(s=0\). Moreover
  \[
  -4t^2+\frac{32}{5}t-\frac{27}{10}
   =-4\left(t-\frac45\right)^2-\frac7{50},
  \]
  which gives exactly the lower bound \((7/50)^2\).

Thus (6) follows. Notice that the constant is sharp: equality occurs when
\(u=0\) and \(t=4/5\).

We will also use the deliberately crude bounds

\[
 |f|\le\frac{253}{160},\qquad |f_{\bar w}|\le\frac{129}{80},qquad
 |f_{w\bar w}|\le\frac{47}{40},\qquad
 |f_{\bar w\bar w}|\le\frac{47}{40}<5.                               \tag{7}
\]

They follow term by term from \(|\sin|,|\cos|\le1\). For example,
\(|f_x|\le3/2\), \(|f_y|\le69/40\), and
\(|f_{\bar w}|\le(|f_x|+|f_y|)/2=129/80\).

Finally, \(f(-w)=f(w)\). Differentiating twice gives
\(f_{ww}(-w)=f_{ww}(w)\). Because \(f_{ww}\) is nonzero on the simply connected plane, it
has a continuous argument. The evenness forces that argument to be even as well: the possible
difference between the arguments at \(w\) and \(-w\) is a constant multiple of \(2\pi\), and it
is zero at \(w=0\). Consequently the image under \(f_{ww}\) of any closed curve has winding
number zero. This observation handles the half-integral powers occurring for odd \(k\).

## 3. A reusable exponential domination lemma

We use the following standard flatness result.

**Flat exponential lemma.** Let \(a,c>0\), and define

\[
 F_{a,c}(r)=\begin{cases}e^{-c r^{-a}},&r>0,\\0,&r=0.\end{cases}
\]

Then \(F_{a,c}\) is \(C^\infty\) on \([0,\infty)\), every derivative at zero is zero, and,
for every real \(N\),

\[
                    r^{-N}F_{a,c}(r)\longrightarrow0\quad(r\downarrow0). \tag{8}
\]

For formalisation, prove (8) first after the substitution \(t=r^{-a}\): exponential decay
dominates every real power of \(t\). An induction shows that each derivative of \(F_{a,c}\) is
the original exponential multiplied by a finite sum of real powers of \(r\). Equation (8) then
extends every derivative continuously by zero.

Here is the induction in the form needed later. For every \(j\ge0\), there is a finite set
\(S_j\subset\mathbb R\) and constants \(c_{j,\nu}\) such that, for \(r>0\),

\[
 F_{a,c}^{(j)}(r)=F_{a,c}(r)\sum_{\nu\in S_j}c_{j,\nu}r^\nu.           \tag{8a}
\]

The assertion for \(j+1\) follows by differentiating: differentiating a monomial lowers its
exponent by one, while differentiating the exponential introduces the additional factor
\(ca r^{-a-1}\). Thus every summand in (8a) tends to zero at the origin by (8). Induction using
the elementary extension lemma

\[
 u\in C^1((0,\varepsilon)),\quad u(r)\to0,\quad u'(r)\to0
 \quad\Longrightarrow\quad
 \bigl(u(0):=0\bigr)\in C^1([0,\varepsilon))
\]

proves simultaneous smoothness and flatness.

Near zero, \(e^{-r^2}\ge1/2\), and therefore

\[
 0<E(r)\le e^{-\frac12 r^{-1/4}}.                                      \tag{9}
\]

Every derivative of \(E\) is bounded by (9) times a finite sum of negative powers of \(r\).

We also need a quantitative, global version later. If \(a,b>0\), then

\[
 \sup_{y>0}y^a e^{-by}=\left(\frac{a}{be}\right)^a.                    \tag{10}
\]

This follows by differentiating \(a\log y-by\). In Lean it should be a standalone lemma for
`Real.rpow`; all numerical estimates below are rational consequences of (10) and
\(e>8/3\).

## 4. Smoothness of the planar family

On a simply connected sector in the punctured plane choose a branch

\[
 w(z)=\left(100/\bar z\right)^{k/2}.
\]

For odd \(k\), changing the square-root branch replaces \(w\) by \(-w\), and hence does not
change \(f(w)\). Thus the local expressions glue to a single smooth function on
\(\mathbb C\setminus\{0\}\). Equivalently one may use the principal `Complex.cpow`; its jump
across the branch cut is a sign, which disappears after composition with the even function
\(f\).

For every multi-index \(\alpha\), repeated chain and product rules give

\[
 |D^\alpha(A(r)f(w(z)))|\le C_\alpha r^{-N_\alpha}
 e^{-\frac12r^{-1/4}}                                                   \tag{11}
\]

for suitable constants \(C_\alpha,N_\alpha\). Indeed, all derivatives of \(f\) are bounded,
derivatives of \(w\) have at most algebraic growth in \(1/r\), and derivatives of \(A\) are
controlled by (9). Equation (8) makes the right side of (11) tend to zero. Hence the
nonconstant part of \(g_k\), with value zero at the origin, is smooth and flat there. This proves
part 1 of the theorem.

More explicitly, on a closed subsector every derivative of \(w\) is a constant times a power of
\(\bar z\), and hence is \(O(r^{-k/2-j})\) after \(j\) derivatives. Every derivative of \(f\)
is bounded because it is a finite trigonometric polynomial. Finally, differentiating
\(\log E=-r^{-1/4}e^{-r^2}\) shows inductively that \(D^jE/E\) is a finite sum of powers of
\(r\) times bounded smooth functions. These three facts prove (11) term by term through the
multivariable product and chain rules. Since the estimates agree on overlaps and the odd-\(k\)
expressions agree under \(w\mapsto-w\), the sectorwise smooth extensions glue.

## 5. The index at the origin

Work again on a branch sector. The most singular term in two \(\bar z\)-derivatives is

\[
 A(r) f_{ww}(w(z))\,w_{\bar z}(z)^2.                                   \tag{12}
\]

Since

\[
 w_{\bar z}=-\frac{k}{2}\frac{w}{\bar z},
\]

the argument contributed by \(w_{\bar z}^2\) on \(z=re^{i\theta}\) is
\((k+2)\theta\), up to a constant. The factor \(A(r)\) is positive, and the factor
\(f_{ww}(w)\) has winding zero by Section 2.

All other terms are smaller uniformly on the circle as \(r\to0\). More explicitly, relative
to (12):

\[
\begin{array}{c|c}
\text{source of an error term}&\text{upper bound for the relative size}\\ \hline
w_{\bar z\bar z}f_w&r^{k/2}\\
(A_{\bar z}/A)w_{\bar z}f_w&r^{k/2-1/4}\\
(A_{\bar z\bar z}/A)f&r^{k-1/2}\\
\dfrac{2z}{1+r^2}(A f(w))_{\bar z}&r^{k/2+2}.
\end{array}                                                            \tag{13}
\]

The bounded derivatives in the numerators and the lower bound (6) make the estimates uniform.
Every exponent in (13) is positive when \(k\ge1\). Therefore, on all sufficiently small
circles, the full Euclidean operator (2), and also the spherical operator (3), are joined to
(12) by the straight-line homotopy without crossing zero. Their winding number is thus
\(k+2\), and the principal-line index is \(1+k/2\). This proves part 2.

The same domination on a punctured disc shows that the zero at the origin is isolated, rather
than merely giving the winding on a selected sequence of circles.

## 6. The second chart for \(g_2\)

For \(k=2\), introduce the reciprocal coordinate

\[
                         w=100/\bar z.
\]

Writing \(s=|w|^2\), the nonconstant part of \(g_2\) becomes

\[
 h_0(w)=B(s)f(w),                                                       \tag{14}
\]

where

\[
 B(s)=\frac{10000}{s+10000}e^{-\psi(s)},\qquad
 \psi(s)=\left(\frac{s}{10000}\right)^{1/8}e^{-10000/s}                \tag{15}
\]

for \(s>0\), and \(\psi(0)=0\). The flat exponential lemma applied to
\(e^{-10000/s}\) shows that \(\psi\), then \(B\), is smooth at zero, with \(B(0)=1\).
Thus (14) extends smoothly through \(w=0\), the point \(z=\infty\). Together with Section 4,
this proves part 3.

In this chart the round metric is

\[
 ds^2=\frac{40000}{(s+10000)^2}|dw|^2.                                 \tag{16}
\]

Consequently its spherical umbilic operator is

\[
 Q_w(h)=h_{\bar w\bar w}+\frac{2w}{s+10000}h_{\bar w}.                 \tag{17}
\]

## 7. The cancellation proving uniqueness

Let \(D=s+10000\), \(p=\psi'(s)\), and \(L=(\log B)'=-1/D-p\). Radial
differentiation gives

\[
 B_{\bar w}=BLw,\qquad B_{\bar w\bar w}=B(L^2+L')w^2.
\]

Substitute these identities into (17). The derivatives of the rational factor \(10000/D\)
cancel the Christoffel term exactly, leaving

\[
 \boxed{\frac{Q_w(Bf)}B
 =f_{\bar w\bar w}-2wp f_{\bar w}+w^2(p^2-p')f.}                        \tag{18}
\]

This cancellation is the reason for the factor \(|z|^2/(1+|z|^2)\) in (1).

It remains to bound the last two terms in (18). Put \(x=s/10000\) and
\(\phi(x)=x^{1/8}e^{-1/x}\), so that \(\psi(s)=\phi(x)\). Direct differentiation gives

\[
\begin{aligned}
 \sqrt{x}\,\phi'(x)
 &=e^{-y}\left(\frac18y^{3/8}+y^{11/8}\right),\\
 x\phi'(x)^2
 &=e^{-2y}\left(\frac1{64}y^{3/4}+\frac14y^{7/4}+y^{11/4}\right),\\
 x\phi''(x)
 &=e^{-y}\left(-\frac7{64}y^{7/8}-\frac74y^{15/8}+y^{23/8}\right),
                                                                            \tag{19}
\end{aligned}
\]

where \(y=1/x\). Formula (10), with the crude estimate \(e>2\), yields

\[
 |wp|\le\frac1{100},\qquad |w^2(p^2-p')|\le\frac1{1000}.                \tag{20}
\]

For clarity, the first numerator in (19) is at most one: the first summand is at most
\(1/8\), while the second has maximum
\((11/(8e))^{11/8}<7/8\). For the second estimate, the triangle inequality bounds the sum of
the six terms in the last two lines of (19) by ten. One completely rational certificate is as
follows. Using \(e>2\), the three maxima in the line containing \(e^{-2y}\), including their
coefficients, are respectively less than \(1/64,1/4,1\). The three maxima in the line containing
\(e^{-y}\) are less than \(7/64,7/4,3\); for the last one use
\[
 (23/(8e))^{23/8}<(23/16)^{23/8}<(23/16)^3<3.
\]
Their sum is less than \(10\). After restoring the factor \(1/10000\) coming from
\(s=10000x\), this is the second inequality in (20). These intentionally loose rational bounds
are convenient in Lean.

Combining (6), (7), (18), and (20),

\[
\begin{aligned}
 \left|\frac{Q_w(Bf)}B-f_{\bar w\bar w}\right|
 &\le 2\cdot\frac1{100}\cdot\frac{129}{80}
       +\frac1{1000}\cdot\frac{253}{160}\\
 &=\frac{5413}{160000}<\frac7{200}
 \le |f_{\bar w\bar w}|.                                               \tag{21}
\end{aligned}
\]

Since \(B>0\), (21) proves that \(Q_w(h_0)\ne0\) at every finite \(w\). Finite \(w\)
parametrizes the entire sphere except the point \(z=0\). At that remaining point, Section 4
shows that \(h_0\) is flat, hence umbilic. This proves part 4: it is the unique umbilic.

## 8. Convexity and the constant \(10^{10}\)

For a smooth function \(h\) on \(S^2\), define the radius-of-curvature tensor

\[
                        R_h=\nabla^2h+h g_{S^2}.                         \tag{22}
\]

We need a numerical upper bound for \(R_{h_0}\), where \(h_0=Bf\). The following coarse bound
is more than sufficient and is chosen to have a short formal proof:

\[
                         \|R_{h_0}\|_{\mathrm{op}}<3\cdot10^9.          \tag{23}
\]

Here is a certificate for (23). In the \(w\)-chart put

\[
 y=(s/10000)^{1/8},\qquad \psi=y e^{-y^{-8}},\qquad
 M(y)=\lambda^{-2}B=\frac{s+10000}{4}e^{-\psi}
      =2500(1+y^8)e^{-\psi}.                                            \tag{24}
\]

- For \(0\le y\le2\), \(M(y)\le642500\).
- For \(y\ge2\), the inequality \(e^{-y^{-8}}\ge1-y^{-8}\ge255/256\), followed by
  (10) and \(e>8/3\), gives
  \[
    M(y)\le2500\left(1+\sup_{y>0}y^8e^{-(255/256)y}\right)
      <2500(1+4^8)<1.64\cdot10^8.                                      \tag{25}
  \]

Thus \(M<1.64\cdot10^8\) globally. Equation (18), the sharper upper bound
\(|f_{\bar w\bar w}|\le47/40\) in (7), and (20) give the deliberately loose estimate

\[
 \frac{|Q_w(h_0)|}{B}
 \le\frac{47}{40}+\frac{258}{8000}+\frac{253}{160000}<5,
 \qquad\text{hence}\qquad |Q_w(h_0)|\le5B.                              \tag{26}
\]

The operator norm of the trace-free spherical Hessian is
\(2\lambda^{-2}|Q_w(h_0)|\), so (25)–(26) bound it by
\(1.64\cdot10^9\).

For the trace, radial differentiation gives

\[
 \frac{(Bf)_{w\bar w}}B
 =f_{w\bar w}+L(wf_w+\bar w f_{\bar w})
   +\left(L+s(L^2+L')\right)f.                                         \tag{27}
\]

Besides (20), formulas (19) and (10) give

\[
 |p|\le\frac2{10000},\quad
 \frac{|w|}{D}\le\frac1{200},\quad
 \frac{s}{D^2}\le\frac1{40000}.                                      \tag{28}
\]

For completeness, after substituting \(L=-1/D-p\), the last coefficient in (27) is

\[
 L+s(L^2+L')=-\frac1D-p+s\left(\frac2{D^2}+\frac{2p}{D}+p^2-p'\right).
\]

Now (7), (20), (28), and \(s/D\le1\) give

\[
\begin{aligned}
 \left|\frac{(Bf)_{w\bar w}}B\right|
 &\le \frac{47}{40}
   +2\left(\frac1{200}+\frac1{100}\right)\frac{129}{80}\\
 &\quad+\left(\frac1{10000}+\frac2{10000}+\frac1{20000}
                    +\frac1{2500}+\frac1{1000}\right)\frac{253}{160}\\
 &=\frac{784731}{640000}<2.                                           \tag{29}
\end{aligned}
\]

The scalar part of the spherical Hessian has norm
\(2\lambda^{-2}|(Bf)_{w\bar w}|<4M<6.56\cdot10^8\). Also \(B\le1\), so
\(|h_0|\le253/160<2\). Consequently

\[
 \|R_{h_0}\|_{\mathrm{op}}
 <10M+4M+2
 <2.296\cdot10^9+2
 <3\cdot10^9,
\]

which proves (23).

Now set \(h=10^{10}+h_0\). Since the Hessian of a constant is zero,

\[
 R_h=10^{10}g_{S^2}+R_{h_0}.
\]

By (23), every eigenvalue of \(R_h\) is positive. In fact it is greater than
\(7\cdot10^9\). Thus \(R_h\) is positive definite everywhere.

The standard support-function construction is

\[
 X_h(u)=h(u)u+\nabla h(u),\qquad u\in S^2.                              \tag{30}
\]

Its derivative on \(T_uS^2\) is \(R_h\), and its unit normal is \(u\). Positive definiteness
of \(R_h\) implies that (30) is the Gauss parametrization of the boundary of the compact strictly
convex body

\[
 K_h=\{x\in\mathbb R^3:\langle x,u\rangle\le h(u)\text{ for every }u\in S^2\}.
\]

The shape operator is \(R_h^{-1}\). Therefore a point of this convex surface is umbilic exactly
when the trace-free part of \(R_h\), equivalently the trace-free part of \(\nabla^2h\), vanishes.
The constant \(10^{10}\) affects neither this trace-free tensor nor its zeros. Section 7 therefore
shows that the surface has exactly one umbilic. This proves part 5 and the announced
Carathéodory counterexample.

## 9. Lean decomposition

The Lean development should follow this dependency order.

1. **Wirtinger API.** Define first and second Wirtinger derivatives as real Fréchet derivatives,
   and prove that `traceFreeHessian = 4 • wirtingerBar (wirtingerBar f)`.
2. **Seed identities.** Prove (4), evenness, the bounds (7), and the three-case polynomial
   certificate (6). These are finite `ring_nf`/`nlinarith` arguments after trigonometric bounds.
3. **Flat functions.** Prove (8)–(10) in a reusable file under `FormalConjecturesForMathlib`.
   This file must contain no `sorry`.
4. **Branch-independent power.** Package `f ((100 / star z) ^ (k/2))` as a smooth function on
   the punctured plane. For odd `k`, glue the two square-root branches using `f (-w) = f w`.
5. **Smooth extension at zero.** Turn (11) into a general extension lemma and instantiate it.
6. **Index.** Expand the Hessian, prove the relative estimates (13), and use homotopy invariance
   of winding number to obtain `2 + k`.
7. **Sphere charts.** Define the two chart representatives, prove their transition identity,
   and derive the spherical operators (3) and (17).
8. **Uniqueness.** Formalize (18)–(21). This part should use only differentiation, rational
   inequalities, and the seed certificate.
9. **Support functions.** Define (22) and (30), prove the support-function theorem, formalize
   the numerical certificate (23), and conclude strict convexity and uniqueness of the umbilic.

The first four analytic estimates should be proved independently of the particular surface; this
keeps the problem file short and leaves generally useful flatness and support-function API in
`FormalConjecturesForMathlib`.
