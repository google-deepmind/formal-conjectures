# Epstein lattice / Euler-product Weil control V1

Status: **T1 numerical diagnostic only**. No global Weil positivity and no RH
claim is made by this experiment.

## Why the D = -20 same-discriminant control is the clean comparison

For the principal binary quadratic form

[
Q_1(x,y)=x^2+5y^2,qquad D=-20,
]

the Epstein zeta is not itself an Euler product. The class-sum / Dedekind
control

[
A(s)=zeta(s)L(s,chi_{-20})
]

*is* an Euler product. Both have the same discriminant and therefore the same
completed degree-two conductor/gamma factor. This removes the conductor and
Archimedean term as explanations of a spectral difference.

Coefficientwise, the class-number-two decomposition is

[
E_{Q_1}(s)=A(s)+B(s),qquad
B(s)=L(s,chi_{-4})L(s,chi_5).
]

The test suite independently reconstructs the coefficients from lattice-point
counts and verifies this identity on a finite prefix.

## Exact finite arithmetic falsifier

Normalize (E_{Q_1}/2) so its first Dirichlet coefficient is one. Its first
coefficients include

- (a(2)=0),
- (a(3)=0),
- (a(4)=1),
- (a(5)=1),
- (a(6)=2).

For

[
-rac{F'}{F}(s)=sum_{nge 2}rac{Lambda_F(n)}{n^s},
]

the exact Dirichlet-convolution recurrence gives

[
Lambda_F(6)=2log 6
e0.
]

Because 6 is not a prime power, this is a finite certificate that the
principal Epstein zeta lacks an Euler product. By contrast, the same
finite-prefix checker finds prime-power-only support for
(zeta(s)L(s,chi_{-20})).

## Finite Galerkin control at L = 3.5

The probe uses the moment-zero family already used by the AEGIS
`krein_dual_beyond_log2.py` lane,

[
g=(1/4-D^2){sin(pi x/L)sin(kpi x/L)},
]

and the completed degree-two critical-line symbol

[
S_D(t)=2Repsi(1/2+it)
 +2lograc{sqrt{|D|}}{2pi}
 -2sum_{log n<L}rac{Lambda_F(n)}{sqrt n}cos(tlog n).
]

A CI-sized configuration (`basis_dim=24`, (T=600), (dt=0.05)) gives a
robust sign separation:

- principal (x^2+5y^2): minimum generalized eigenvalue < (-0.25);
- Euler class-sum (zeta L(chi_{-20})): minimum generalized eigenvalue > (+0.15);
- the principal negative minimizer evaluated on the Euler control is > (+1).

A stronger local stress run (not encoded as a CI threshold) with
`basis_dim=60`, (T=3000), (dt=0.02) gave approximately

- principal: (-0.4835724241);
- Euler class-sum: (+0.1958097947);
- same principal witness on Euler control: (+6.764880123).

These are floating-point finite-section diagnostics. The negative principal
witness is a concrete candidate for interval/ARB certification; the positive
Euler finite section is **not** a global positivity theorem.

## Independent zero-side check

Numerically, the principal (D=-20) Epstein zeta has an off-critical zero at

[

hoapprox
0.8231873164780866676470730774
+44.00011318023689727806224695,i.
]

At 80 decimal digits, evaluating

[
A(s)=zeta(s)L(s,chi_{-20}),qquad
B(s)=L(s,chi_{-4})L(s,chi_5)
]

via Hurwitz-zeta Dirichlet-(L) evaluation gives
(|A(
ho)+B(
ho)|<4	imes10^{-80}), while
(|A(
ho)|=|B(
ho)|approx0.7758158509) and
(A(
ho)/B(
ho)=-1) to the working precision. Thus the observed zero comes
from cancellation between two nonzero Euler-product components rather than a
zero of either component.

This numerical observation agrees with the classical
Davenport--Heilbronn/Voronin phenomenon for Epstein zeta functions of class
number greater than one.

## Next promotion step

Export the 60-dimensional negative principal witness and certify its quadratic
value with interval/ARB arithmetic, including a rigorous tail bound in (t).
Only that negative witness needs certification; no claim of positivity for the
Euler control is required for the falsifier.


## Optimizer-free seven-mode witness

A sparse integer witness removes generalized-eigensolver dependence from the
sign separation.  In the even modes

[
k=(4,6,8,10,12,16,18)
]

use the integer coefficient vector

[
c=(22,10,6,3,2,-2,-1).
]

For the committed CI-sized quadrature ((L,N,T,dt)=(3.5,24,600,0.05)), direct
Rayleigh evaluation gives approximately

- principal (x^2+5y^2): (-0.071782623);
- Euler class-sum (zeta(s)L(s,chi_{-20})): (+5.361928445).

The same vector therefore gives a large same-discriminant sign contrast without
calling an eigensolver during evaluation.  Independent stress checks show the
principal value moving toward roughly (-0.065) as (T) is increased from
600 to 20000, while halving the quadrature step from 0.05 to 0.0125 changes the
(T=600) value by only about (5.2	imes10^{-9}).

These stability checks are numerical, not interval bounds.  The next rigorous
promotion is now narrower: certify this fixed seven-mode quadratic value and an
upper bound for its omitted (t>T) tail.


## Arithmetic-mode decomposition: where the sign gap comes from

Because the principal Epstein object and the Euler class-sum control both have
discriminant (-20), their completed conductor and Gamma contribution are
identical.  On the fixed seven-mode witness their difference is therefore
purely arithmetic.

Using Parseval,

[
rac1piint_0^infty |widehat g(t)|^2cos(tu),dt
  = int g(x)g(x+u),dx,
]

so every arithmetic frequency can be evaluated directly in x-space at
(u=log n), with no t-grid and no Archimedean tail.

For (L=3.5), the fixed witness gives

- total principal-minus-Euler arithmetic shift: approximately
  (-5.433709725);
- shift from non-prime-power support alone: approximately
  (-2.610467055);
- shift from altered prime-power weights: approximately
  (-2.823242670).

The first forbidden composite mode is already decisive:

[
n=6,qquad Lambda_{
m principal}(6)=2log 6,qquad
Lambda_{
m Euler}(6)=0,
]

and its contribution to the normalized principal-minus-Euler quadratic value
is approximately (-1.067827356).

Further non-prime-power modes inside the same support window include (n=14)
and (n=21).  Together (6,14,21) account for about 48% of the full
same-discriminant arithmetic shift.

This does not prove a general theorem that "Euler product implies Weil
positivity".  It does establish a much sharper bounded mechanism: for this
same-discriminant pair and this explicit fixed test function, the loss of
prime-power-only logarithmic-derivative support produces a large negative
quadratic displacement while all Archimedean data cancel from the comparison.


## Quadratic Euler first-impulse table

For a class-number-one quadratic Dedekind/Epstein Euler product

[
F_D(s)=zeta(s)L(s,chi_D),
]

the logarithmic derivative has local coefficient

[
Lambda_D(p^m)=log p,[1+chi_D(p)^m].
]

This immediately separates the local cases:

- split: (chi_D(p)=1), so every (p^m) contributes (2log p);
- ramified: (chi_D(p)=0), so every (p^m) contributes (log p);
- inert: (chi_D(p)=-1), so odd powers vanish and even powers contribute
  (2log p).

The committed exact-integer character test therefore gives:

| lattice / discriminant | first nonzero logarithmic-derivative mode | reason |
| --- | ---: | --- |
| square / (D=-4) | (n=2) | 2 ramified |
| hexagonal A2 / (D=-3) | (n=3) | 2 inert, but 3 ramified before (2^2) |
| Heegner (D=-19) | (n=4=2^2) | 2 inert |
| Heegner (D=-163) | (n=4=2^2) | 2 inert |

Thus the silent support windows satisfy

[
log 2 < log 3 < log 4.
]

The (D=-19) and (D=-163) cases saturate the largest possible first window
caused solely by the local factor at the smallest rational prime: an inert 2
reappears at (2^2=4).  This also shows why the first-window length alone
cannot characterize the Euler product; prime-power purity of the complete
logarithmic derivative is the stronger invariant.

## Formula-to-target identity: machine-formalization status

The t-space target form used by `assemble_quadratic_matrix` is
(1/π)∫₀^∞ |ĝ(t)|² S(t) dt with
S(t) = 2 Re ψ(1/2+it) + log(5/π²) − 2 Σ Λ_F(n) n^{-1/2} cos(t log n).
It involves no zeros. Passing to the x-space value certified by
`certify_d20_fixed_witness_absolute_quadratic` needs three analytic inputs.
Lean status (Lean 4.33.1 / Mathlib 0df444a3, standard axioms only):

| input | status |
| --- | --- |
| ψ(1/2) = −γ − 2 log 2 | proved (`EpsteinWeilXSpaceIdentityV1.epsteinWeil_digamma_one_half_re_v1`) |
| ∫_L^∞ du/sinh(u/2) = 2(log(1+e^{-L/2}) − log(1−e^{-L/2})) | proved (`EpsteinWeilXSpaceIdentityV1.sinhHalf_tail_integral_v1`) |
| Gauss: Re ψ(1/2+it) − ψ(1/2) = ∫₀^∞ (1−cos tu)/(2 sinh(u/2)) du | proved (`EpsteinGaussCriticalLineV1.gauss_critical_line_v1`), specializing the existing `WeilDigammaSeriesHalfPlaneV1.gauss_digamma_integral_v1` (already on this branch) |
| Parseval/cosine: (1/π)∫₀^∞ \|ĝ\|² cos(tu) dt = h(u) and the Fubini swap | open |

`FORMULA_TO_TARGET_WEIL_IDENTITY_FORMALIZED` stays `FALSE`.
