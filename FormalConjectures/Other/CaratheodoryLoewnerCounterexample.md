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

There are two normalizations to keep separate in the Lean development. The repository's
`traceFreeHessian` is \(q_{\mathrm E}=4u_{\bar z\bar z}\). In a chart whose metric is

\[
 ds^2=\lambda^2|dw|^2,
\]

the Lean expression called `sphericalTraceFreeHessian` is

\[
 q_{\mathrm E}(u)+8\frac{w}{D}u_{\bar w}=4Q_w(u),                       \tag{3a}
\]

where \(D=1+|w|^2\) in the original chart and \(D=10000+|w|^2\) in the
reciprocal chart. The anti-linear coefficient of the metric-raised trace-free Hessian is

\[
 2\lambda^{-2}Q_w(u)=\frac{\lambda^{-2}}2
   \operatorname{sphericalTFH}(u).                                      \tag{3b}
\]

In the reciprocal chart, where \(\lambda^2=40000/D^2\), this coefficient is exactly

\[
 \frac{D^2}{80000}\operatorname{sphericalTFH}(u).                       \tag{3c}
\]

Thus the \(Q\)-normalization is convenient for the estimates below, while (3a)--(3c) give the
literal constants needed to translate them to the current Lean definitions.

We prove the following more explicit result.

**Theorem.**

1. Every \(g_k\) is \(C^\infty\) at the origin.
2. If \(k>0\), the origin is an isolated zero of the Euclidean operator (2), with winding
   number \(k+2\) there.
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

Finally, \(f(-w)=f(w)\). Since \(f\) is real valued,
\(f_{ww}=\overline{f_{\bar w\bar w}}\), so (6) also gives

\[
 |f_{ww}|\ge \frac7{200}.
\]

Differentiating the evenness twice gives \(f_{ww}(-w)=f_{ww}(w)\). Because \(f_{ww}\) is
nonzero on the simply connected plane, it
has a continuous argument. The evenness forces that argument to be even as well: the possible
difference between the arguments at \(w\) and \(-w\) is a constant multiple of \(2\pi\), and it
is zero at \(w=0\). Consequently the image under \(f_{ww}\) of any closed curve has winding
number zero. More particularly, when \(k\) is odd the continuously chosen branch path
\(w(\theta)\) runs from \(w(0)\) to \(-w(0)\); the even argument has equal endpoint values, so
its total argument change is still zero. This observation handles the half-integral powers
occurring for odd \(k\).

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

This follows by differentiating \(a\log y-by\). The development proves the required
`Real.rpow` inequalities locally in `Global.lean`, since only this numerical certificate uses
them; all numerical estimates below are rational consequences of (10) and \(e>8/3\).

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
 L_k(z):=A(r) f_{ww}(w(z))\,w_{\bar z}(z)^2.                            \tag{12}
\]

Since

\[
 w_{\bar z}=-\frac{k}{2}\frac{w}{\bar z},
\]

the argument contributed by \(w_{\bar z}^2\) on \(z=re^{i\theta}\) is
\((k+2)\theta\), up to a constant. The factor \(A(r)\) is positive, and the factor
\(f_{ww}(w)\) has winding zero by Section 2. Changing an odd-\(k\) branch sends both
\(w\) and \(w_{\bar z}\) to their negatives; evenness of \(f_{ww}\) and the square on
\(w_{\bar z}\) therefore make \(L_k\) a single-valued function.

We now make the domination uniform on one punctured disc. On every branch,

\[
\begin{aligned}
 (Af(w))_{\bar z\bar z}
  &=L_k
    +A f_w(w)w_{\bar z\bar z}
    +2A_{\bar z}f_w(w)w_{\bar z}
    +A_{\bar z\bar z}f(w).                                             \tag{12a}
\end{aligned}
\]

For \(0<r\le r_0\), direct differentiation of \(\log A\) gives constants
\(C_1,C_2>0\), independent of the angle, such that

\[
 \frac{|A_{\bar z}|}{A}\le C_1r^{-5/4},\qquad
 \frac{|A_{\bar z\bar z}|}{A}\le C_2r^{-5/2}.                          \tag{12b}
\]

Also

\[
\begin{aligned}
 |w|&=100^{k/2}r^{-k/2},\\
 |w_{\bar z}|&=\frac{k}{2}\frac{|w|}{r},\\
 |w_{\bar z\bar z}|&=\frac{k}{2}\left(\frac{k}{2}+1\right)
                       \frac{|w|}{r^2}.                               \tag{12c}
\end{aligned}
\]

Using (6)--(7), (12b), and (12c), there are constants \(C_{j,k}\) such that the
ratios to \(|L_k|\) have the following uniform asymptotic orders:

\[
\begin{array}{c|c}
\text{source of an error term}&\text{relative norm}\\ \hline
A f_w w_{\bar z\bar z}
  &\dfrac{|A f_w w_{\bar z\bar z}|}{|L_k|}\le C_{1,k}r^{k/2}\\
2A_{\bar z}f_w w_{\bar z}
  &\dfrac{|2A_{\bar z}f_w w_{\bar z}|}{|L_k|}\le C_{2,k}r^{k/2-1/4}\\
A_{\bar z\bar z}f
  &\dfrac{|A_{\bar z\bar z}f|}{|L_k|}\le C_{3,k}r^{k-1/2}.
\end{array}                                                            \tag{13}
\]

The factors \(100^{k/2}\), \(k/2\), and the bounds in (7) are absorbed only in the constants
\(C_{j,k}\), not in the powers of \(r\). This is the literal meaning of the often-used shorthand
\(O_k(r^\alpha)\) here. Put

\[
 \alpha_k=\min\left\{\frac k2,\frac k2-\frac14,k-\frac12\right\}>0.
\]

After shrinking \(r_0\) to at most one and taking \(C_k\) to be the sum of the three constants,
the normalized Euclidean error is bounded by \(C_kr^{\alpha_k}|L_k|\):

\[
 \left|\frac14q_{\mathrm E}(g_k)-L_k\right|
   \le C_kr^{\alpha_k}|L_k|.                                           \tag{13a}
\]

Here \(L_k(z)\ne0\) on the punctured plane: \(A(r)>0\), (6) gives
\(|f_{ww}|\ge7/200\), and \(w_{\bar z}\ne0\) for \(k>0\).
The factor \(1/4\) is essential: the Euclidean operator (2) has leading term \(4L_k\).
Choose one \(\delta_k\in(0,r_0)\) with \(C_k\delta_k^{\alpha_k}<1\). Then (13a) holds with
strict error smaller than the leading norm for every \(0<|z|<\delta_k\), not only on a
sequence of circles. The straight-line homotopy from \(\frac14q_{\mathrm E}(g_k)\) to \(L_k\)
therefore never meets zero on any circle of radius \(r<\delta_k\). It also proves nonvanishing
throughout the punctured disc, so the zero at the origin is isolated.

For completeness, choose a continuous branch \(w_r(\theta)\) on \(0\le\theta\le2\pi\).
The even continuous argument of \(f_{ww}\) from Section 2 has equal values at the two endpoints,
even when odd \(k\) makes \(w_r(2\pi)=-w_r(0)\). The remaining nonconstant phase of \(L_k\) is
the phase of \(w_{\bar z}^2\), so a lift of its normalized argument changes by
\(2\pi(k+2)\). Extend this lift to all \(\theta\in\mathbb R\) by adding
\(2\pi(k+2)\) on each period. The normalized straight-line homotopy lifts through the
exponential covering, and its endpoint difference is constant during the homotopy. The
Euclidean trace-free Hessian therefore has winding number \(k+2\), and the principal-line index is
\(1+k/2\). This proves part 2. The spherical calculation needed for the global counterexample
is carried out separately for \(k=2\) in Sections 6--8.

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
Multiplying (18) by four gives exactly the normalization used in Lean:

\[
 \frac{\operatorname{sphericalTFH}(Bf)}B
 =q_{\mathrm E}(f)-8wp\,\operatorname{complexBarDeriv}(f)
      +4w^2(p^2-p')f.                                                   \tag{18a}
\]

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

The derivation through \(y=1/x\) applies when \(w\ne0\). At \(w=0\), the smooth extension of
\(\psi\) is flat, so \(p(0)=p'(0)=0\), while \(B(0)=1\). Formula (18), evaluated using these
extended derivatives, reduces to

\[
 Q_0(Bf)=f_{\bar w\bar w}(0)\ne0
\]

by (6). Thus, since \(B>0\), (21) and this separate origin calculation prove that
\(Q_w(h_0)\ne0\) at every finite reciprocal coordinate \(w\). Finite \(w\) parametrizes the
entire sphere except the point \(z=0\) of the original chart. At that remaining point, Section 4
shows that the nonconstant part is flat, so its spherical trace-free Hessian vanishes. This proves
part 4 at the level of the spherical Hessian; Section 8 identifies this condition with
`EuclideanHypersurface.IsUmbilic`, the repository's fundamental-form predicate.

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

At \(y=0\), the expression \(y e^{-y^{-8}}\) in (24) means its continuous value zero; all
subsequent uses of a negative power of \(y\) occur only in the case \(y>0\).

- For \(0\le y\le2\), \(M(y)\le642500\).
- For \(y\ge2\), the inequality \(e^{-y^{-8}}\ge1-y^{-8}\ge255/256\), followed by
  (10) and \(e>8/3\), gives
  \[
    M(y)\le2500\left(1+\sup_{y>0}y^8e^{-(255/256)y}\right)
      <2500(1+4^8)<1.64\cdot10^8.                                      \tag{25}
  \]

Thus \(M<1.64\cdot10^8\) throughout the finite reciprocal chart. Equation (18), the sharper
upper bound \(|f_{\bar w\bar w}|\le47/40\) in (7), and (20) give the deliberately loose
estimate

\[
 \frac{|Q_w(h_0)|}{B}
 \le\frac{47}{40}+\frac{258}{8000}+\frac{253}{160000}<5,
 \qquad\text{hence}\qquad |Q_w(h_0)|\le5B.                              \tag{26}
\]

The operator norm of the metric-raised trace-free spherical Hessian is
\(2\lambda^{-2}|Q_w(h_0)|\). Equivalently, (3a)--(3c) give

\[
 \frac{D^2}{80000}|\operatorname{sphericalTFH}(h_0)|
 =\frac{D^2}{80000}|4Q_w(h_0)|
 =2\lambda^{-2}|Q_w(h_0)|.
\]

Thus (25)--(26) bound it by \(1.64\cdot10^9\).

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

The scalar part of the metric-raised spherical Hessian has norm
\(2\lambda^{-2}|(Bf)_{w\bar w}|<4M<6.56\cdot10^8\). Also \(B\le1\), so
\(|h_0|\le253/160<2\). Consequently

\[
 \|R_{h_0}\|_{\mathrm{op}}
 <10M+4M+2
 <2.296\cdot10^9+2
 <3\cdot10^9,
\]

This proves (23) at every point represented by a finite reciprocal coordinate. That chart omits
the south pole \(z=0\) of the original chart. There the nonconstant part \(h_0\), together with
its first and second derivatives, vanishes by Section 4. Hence \(R_{h_0}=0\) at the omitted
point, and (23) is genuinely global.

Now set \(h=10^{10}+h_0\). Since the Hessian of a constant is zero,

\[
 R_h=10^{10}g_{S^2}+R_{h_0}.
\]

By (23), every eigenvalue of \(R_h\) is positive. In fact it is greater than
\(7\cdot10^9\). Thus \(R_h\) is positive definite everywhere.

We also have the pointwise lower bound

\[
 h\ge 10^{10}-\frac{253}{160}>1,                                      \tag{29a}
\]

because \(0<B\le1\) in the reciprocal chart, and the same estimate follows directly from (1)
in the original chart.

We now give the global support-function argument rather than invoking it as a black box. Let
\(H:\mathbb R^3\to\mathbb R\) be the degree-one radial extension

\[
 H(0)=0,\qquad H(x)=|x|h(x/|x|)\quad(x\ne0),
\]

and put

\[
 X_h(u)=\nabla H(u)=h(u)u+\nabla_{S^2}h(u),\qquad u\in S^2.             \tag{30}
\]

Euler's identity for the homogeneous function gives

\[
 \langle X_h(u),u\rangle=h(u).                                        \tag{31}
\]

After identifying \(T_uS^2\) with its tangent plane in \(\mathbb R^3\), and using the metric to
identify it with its dual, the derivative of \(X_h\) is the raised radius operator

\[
 dX_h=R_h^\sharp:=g_{S^2}^{-1}R_h.                                    \tag{32}
\]

In particular, (23) makes \(dX_h\) injective and tangent to the sphere at \(u\); hence \(u\) is
the chosen unit normal.

It remains to prove the global supporting inequality. If \(u\ne v\) are not antipodal, the
chord

\[
 \gamma(t)=(1-t)u+tv,\qquad 0\le t\le1,
\]

does not meet the origin. The Hessian of \(H\) has the radial direction as kernel and, on
tangent directions at \(rp\), is \(r^{-1}R_h^\sharp\). The chord velocity \(v-u\) is never
radial along this chord unless \(u\) and \(v\) are collinear. Positive definiteness of \(R_h\)
therefore gives

\[
 \frac{d^2}{dt^2}H(\gamma(t))>0.
\]

Strict convexity on the chord and the derivative at \(t=0\) give

\[
 \langle X_h(u),v-u\rangle<h(v)-h(u),
\]

and (31) simplifies this to

\[
 \langle X_h(u),v\rangle<h(v).                                        \tag{33}
\]

If \(v=-u\), then instead

\[
 \langle X_h(u),v\rangle=-h(u)<h(-u)
\]

by (29a). Thus (33) holds for every pair \(u\ne v\), while equality holds for \(u=v\).
Consequently, for every \(x\ne0\), with \(v=x/|x|\),

\[
 \langle X_h(u),x\rangle\le |x|h(v)=H(x),
\]

with equality at \(u=v\). Therefore \(H\) is the supremum of the linear functionals
\(x\mapsto\langle X_h(u),x\rangle\), and in particular is convex.

Define

\[
 K_h=\{x\in\mathbb R^3:\langle x,u\rangle\le h(u)\text{ for every }u\in S^2\}.
\]

This is an intersection of closed half-spaces, hence is closed and convex. Equation (29a) puts
the open unit ball in its interior. It is bounded: if \(x\in K_h\) and \(x\ne0\), choosing
\(u=x/|x|\) gives \(|x|\le h(u)\le\max_{S^2}h\). Thus \(K_h\) is compact and has nonempty
interior. Equations (31) and (33) show that \(X_h(u)\in K_h\), with its unique contact
hyperplane having outer normal \(u\).

The range of \(X_h\) is exactly \(\partial K_h\). One inclusion follows because a point
\(X_h(u)\) lies in \(K_h\) and on a supporting hyperplane, so it cannot be interior. Conversely,
let \(x\in\partial K_h\). The finite-dimensional supporting-hyperplane theorem gives a unit
normal \(u\) at \(x\). The defining inequality for \(K_h\), together with
\(X_h(u)\in K_h\), forces

\[
 \langle x,u\rangle=h(u).
\]

Membership in \(K_h\) says that the linear function \(y\mapsto\langle x,y\rangle\) lies below
the convex homogeneous function \(H\), with equality at \(u\). Since \(H\) is differentiable
there, its supporting linear functional is unique, and hence \(x=\nabla H(u)=X_h(u)\).

The strict inequality (33) also proves injectivity: if \(X_h(u)=X_h(v)\) for \(u\ne v\), then
pairing with \(v\) contradicts (31). Since \(S^2\) is compact, the continuous injection \(X_h\)
is a topological embedding; (32) makes it an immersion. It is therefore a smooth embedding onto
\(\partial K_h\), with outer unit normal \(n(u)=u\). This supplies all the compactness,
nonempty-interior, embedding, normal, and range conditions in IsConvexSphereOfClass. Moreover,
the differentiability argument above makes the contact point for every supporting normal unique,
so every supporting face is a singleton and \(K_h\) is strictly convex.

We finish by spelling out the umbilic bridge. In a conformal complex chart
\(\rho:\mathbb C\to S^2\), write \(u=h\circ\rho\). Relative to the chart differential
\(d\rho\), (32) has the form

\[
 dX_h=d\rho\circ R_h^\sharp,\qquad dn=d\rho.
\]

The identity part \(h\,\mathrm{id}\) and the trace part of the Hessian are scalar. By (3b), the
anti-linear coefficient of the remaining trace-free part is
\(2\lambda^{-2}Q(u)\), or equivalently
\(\lambda^{-2}\operatorname{sphericalTFH}(u)/2\). Thus \(R_h^\sharp\) is scalar exactly when
\(Q(u)=0\). In Lean, `EuclideanHypersurface.IsUmbilic` is stated as proportionality of the
second and first fundamental forms. Normality puts the range of \(dX_h\) in the tangent plane,
while coercivity makes \(dX_h\) injective; equality of the two-dimensional ranges then converts
that form
proportionality to \(dn=c\,dX_h\). Since \(R_h^\sharp\) is positive and invertible,

\[
\begin{aligned}
 \operatorname{IsUmbilic}(X_h,n,\rho(w))
 &\Longleftrightarrow \exists c,\ dn=c\,dX_h\\
 &\Longleftrightarrow \exists c,\ \mathrm{id}=cR_h^\sharp\\
 &\Longleftrightarrow Q_w(u)=0.                                      \tag{34}
\end{aligned}
\]

Equivalently, the shape operator is \((R_h^\sharp)^{-1}\), up to the conventional overall sign,
and it is scalar precisely in (34). In the reciprocal chart, the exact anti-linear coefficient
is the quantity \(D^2\operatorname{sphericalTFH}(u)/80000\) from (3c), whose prefactor never
vanishes.

Section 7 shows that this coefficient is nonzero at every finite reciprocal coordinate. At the
one omitted point \(z=0\), the nonconstant part is flat, so the trace-free Hessian vanishes;
there \(R_h=10^{10}g_{S^2}\), and the point is umbilic. Hence it is the unique umbilic. This
proves part 5 and the announced Carathéodory counterexample.

## 9. Lean decomposition

The files and declarations are arranged in the following dependency order. This list records the
current implementation architecture rather than proposing a separate public Wirtinger API.

1. **Definitions.** `CaratheodoryLoewnerCounterexample/Defs.lean` contains
   `counterexampleSeed`, `counterexample`, `counterexampleSphereChart`, and
   `IsSupportParametrization`. These are the source-facing definitions; short one-use analytic
   expressions remain local to the proof modules.

2. **Reusable flatness.**
   `FormalConjecturesForMathlib/Analysis/SpecialFunctions/FlatRpowExp.lean` defines
   `Real.flatRpowExp` and proves its smoothness, zero Taylor series, and domination by arbitrary
   real powers. The general extension lemmas
   `ContDiff.at_zero_of_iteratedFDeriv_isLittleO` and
   `ContDiff.isLittleO_norm_pow_of_iteratedFDeriv_zero` turn punctured estimates into smooth,
   flat extensions. The elementary quantitative bounds corresponding to (10), which are used
   only for this numerical certificate, remain private in `Global.lean`.

3. **Planar smoothness.** `CaratheodoryLoewnerCounterexample/Smooth.lean` proves
   `counterexampleSeed_contDiff`, glues the principal and alternate half-power branches using
   `counterexampleSeed_cpow_eq_alt`, obtains the polynomial derivative estimates behind (11), and
   concludes `counterexample_contDiff`. Its theorem `counterexample_fderiv_fderiv_zero` records
   the exact second-derivative vanishing needed at the planar origin.

4. **Seed and index calculation.** `CaratheodoryLoewnerCounterexample/Index.lean` keeps the
   concrete first-Wirtinger and trace-free-Hessian expressions local as `seedWirtingerModel` and
   `seedTraceFreeHessianModel`. It proves the public seed bounds
   `counterexampleSeed_abs_le`, `counterexampleSeed_wirtinger_norm_upper`,
   `counterexampleSeed_traceFreeHessian_norm_lower`, and
   `counterexampleSeed_traceFreeHessian_norm_upper`. The identity
   `traceFreeHessian_counterexampleSeed` connects the local model to the repository definition.
   The three-case certificate for (6) is a finite ring-normalization and nonlinear-arithmetic
   proof.

5. **Dominant Hessian and winding.** The same `Index.lean` file defines local
   `counterexampleHessianLeading` and `counterexampleHessianError` and proves
   `counterexample_traceFreeHessian_decomposition`. Three positive powers tend to zero on the
   punctured neighbourhood, giving one radius for both isolation and the normalized
   straight-line homotopy. The covering-map lift preserves the endpoint argument change
   \(2\pi(k+2)\), and `counterexample_hasIsolatedZeroIndex` stores the resulting integer
   \(2+k\), twice the principal-line index.

6. **Sphere charts.** `CaratheodoryLoewnerCounterexample/Global.lean` defines the reciprocal
   exponent, damping, and chart representative; proves `counterexample_two_reciprocal`; and
   glues it to the original chart in `counterexample_two_sphere_extension`. The reciprocal
   origin and the original south pole are treated separately, exactly as in Sections 6--8.

7. **Spherical trace-free calculation.** `Global.lean` uses the private definitions
   `complexBarDeriv` and `sphericalTraceFreeHessian`. By definition the latter is \(4Q\), as in
   (3a), not \(Q\). The product and radial differentiation lemmas yield the factorization (18a).
   The seed perturbation estimate proves nonvanishing at every finite reciprocal coordinate,
   with a separate proof at \(w=0\). The reciprocal radius formula converts this coordinate
   expression to the anti-linear coefficient of the raised radius operator using exactly the
   multiplier \(D^2/80000\) from (3c).

8. **Reusable support geometry.**
   `FormalConjecturesForMathlib/Geometry/EuclideanHypersurface.lean` packages the first and
   second fundamental forms and proves their umbilicity criterion equivalent to a scalar normal
   differential when the normal derivative's range lies in the immersion derivative's range.
   `FormalConjecturesForMathlib/Geometry/SupportFunctionSphere.lean` supplies `radialExtension`,
   `homogeneousGradient`, `body`, the contact and supporting inequalities, compactness and
   interior lemmas, range-equals-frontier results, and injectivity/embedding from strict
   cross-support. These declarations formalize the general steps following (30), rather than
   duplicating them as problem-specific abbreviations.

9. **Numerical radius tensor and the surface.** `Global.lean` contains the scalar estimates
   behind (19)--(29), packages them as a global radius-tensor bound including the separate
   omitted-south calculation, derives strict convexity on nonantipodal chords, handles antipodal
   chords using \(h\ge1\), and implements the chart differential equivalence (34). The reusable
   support API supplies the body and its Gauss parametrization, culminating in
   `counterexample_two_is_support_function_with_unique_umbilic`.

This decomposition keeps general flat-function and support-function results in
`FormalConjecturesForMathlib`, while the oscillatory branches, seed certificates, numerical
constants, and chart normalizations remain in the problem-specific modules.
