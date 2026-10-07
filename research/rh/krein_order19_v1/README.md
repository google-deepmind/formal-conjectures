# Regenerated order-19 Krein certificate

This packet certifies an **explicit real symbol inequality** by rigorous ball
arithmetic with exact rational coefficients. It does not prove RH, does not
prove the repository Weil-form identity, and is not a Lean kernel proof.
`RH_PROVEN = false`; `authority_effect = NONE`.

## Source binding and result

Inspected source: `Aegis-Omega/AEGIS-OMEGA` commit
`2c3d041b633147ec97c7ef753aa9d157a47bb9f5`.
The original numerical script `research/rh/krein_dual_beyond_log2.py` has Git
blob `cb5aaa842b90b49172bbc129f0e3a8ee93923a84`. It uses hats plus distributions,
and contains no order-19 coefficients. The same commit's `RH_STATUS.md`
records order-8 experiments, not the prompt's order-19 margin 0.1059.
Consequently this is a **new deterministic regeneration**, not a replay or
exactification of an unavailable coefficient list.

Parameters: full support width `L = 4/5`, spline order `19` (degree `18`), knot
step `h = 1/1000`, hat half-width `w = 1/50`. All 204 coefficients are exact
rationals in `certificate.json`, rounded once to denominator `10^10` before
certification. The discovery LP has normalized margin about `0.09399363376`;
the numerical grid minimum is about `0.09396197505`. Those values are only
discovery evidence.

The rigorous computation establishes the smaller rational margin `m = 1/16`.
There are 2199 exact rational intervals covering `[0,300]`. Every interval
has certified normalized excess over `m` greater than `1/100000`. The tail
bound for all `t >= 300` is greater than `1.3719` above `m`. Evenness covers
negative `t`. The independent implementation uses direct trigonometric
series and 256 digamma-series terms instead of the main implementation's
Chebyshev recurrence and 128 terms; all 2199 intervals pass without extra
subdivision.

## Exact analytic statement

Use angular Fourier convention

`Fplus(H)(t) = integral exp(i*t*u) H(u) du`.

Let `sinc(x)=sin(x)/x`, with `sinc(0)=1`, and set

```
W(t) = (t^2 + 1/4)^2
S(t) = Re psi(1/4 + i*t/2) - log(pi)
       - sqrt(2)*log(2)*cos(t*log(2)).
```

For the exact `a_i` (`1 <= i <= 199`) and `b_j` (`0 <= j <= 4`) in the JSON,
let `c = L + 19*h/2 = 1619/2000`, `u_i=L+i*w`, and

```
C(t) = 2*w*sinc(w*t/2)^2 * sum_i a_i*cos(u_i*t)
       + sinc(h*t/2)^19 * sum_j b_j*t^j*q_j(c*t),
q_j(x) = cos(x) if j is even, sin(x) if j is odd.
```

The certified inequality is, for every real `t`,

```
W(t)*(S(t)-1/16) + C(t) >= 0.
```

Mathlib's Fourier convention evaluates this correction at
`xi = -t/(2*pi)`. The integral change of variable also needs its `1/(2*pi)`
Jacobian. This packet does not silently equate the displayed `S` with a
new Lean definition or with the repository form.

## Genuine function and support

Let `U_h = indicator_[0,h]/h`, and let
`p(u) = U_h * ... * U_h (u-L)` be its 19-fold convolution. Equivalently,

```
p(u) = 1/(18! * h^19) * sum_(k=0)^19
       (-1)^k * choose(19,k) * max(u-L-k*h,0)^18.
```

Define `tau_i(u)=max(1-|u-u_i|/w,0)` and the real even function

```
H(u) = sum_i a_i*(tau_i(u)+tau_i(-u))
       + sum_j [b_j*(-1)^floor(j/2)/2] * (p^(j)(u)+p^(j)(-u)).
```

The signs and the factor `1/2` are load-bearing. Integration by parts gives
`Fplus(p^(j))(t)=(-i*t)^j*exp(i*c*t)*sinc(h*t/2)^19`; taking the even part
gives exactly `C(t)` above. This also explains why replacing the spline
columns with unscaled copies or a different derivative parity is invalid.

`p` has support `[4/5,819/1000]`, is `C^17`, and `p^(j)` for `j<=4` is
`C^13` or better. The independent replay verifies all 19 integer identities
`sum_(k=0)^19 (-1)^k*choose(19,k)*k^d=0` for `d<19`, the exact polynomial
cancellations outside the last knot. Every hat is supported outside the
open forbidden window `|u|<4/5`; the first hat starts at `4/5` exactly.
Thus `H` is continuous, compactly supported, and integrable. Its hat Fourier
terms decay as `O(t^-2)` and its spline-derivative terms as `O(t^-15)` or
faster, so its Fourier transform is integrable. These are precisely the
regularity/support hypotheses of `RHKreinPairingV13.krein_pairing` after
the Fourier normalization is transported. Their Lean proofs are not
included in this numerical certificate.

## Whole-interval and tail bounds

For `t>=0`, the real digamma series is

```
Re psi(1/4+i*t/2) = -gamma + sum_(n>=0)
  (1/(n+1) - (n+1/4)/((n+1/4)^2+t^2/4)).
```

Every summand is nondecreasing in `t`. Use the source theorem
`AEGIS.RHEulerGammaV13.gamma_lt`, whose bound is `gamma < 5792/10000`.
After `N` terms, a lower bound for the remaining sum is

```
-(3/4)*(1/(N+1/4) + 1/(N+1/4)^2).
```

Indeed, a summand is at least `1/(n+1)-1/(n+1/4)`, which is at least
`-(3/4)/(n+1/4)^2`; bound the positive decreasing tail by its first term
plus its integral. Both programs therefore use only finite rational
operations for this bound; neither calls a numerical digamma function.

For Taylor enclosures, differentiating a normalized convolution gives
`||p^(j)||_1 <= 2^j/h^j`. Compact support then gives the exact bound

```
|C^(8)(t)| <= M8
M8 = sum_i 2*w*|a_i|*(u_i+w)^8
     + sum_j |b_j|*(2/h)^j*(L+19*h)^8.
```

Both programs construct a degree-7 Fourier Taylor polynomial at the
interval midpoint and add the rigorous remainder `M8*radius^8/8!`.
There is no interpolation or grid-only inference. Endpoints, coefficients,
`M8`, and the subdivision cover are rational; real elementary functions
are enclosed by Arb. Each stored lower endpoint is an integer multiple of
`2^-64`, rounded down using exact integer arithmetic and checked against the
Arb lower endpoint.

For `t>=T=300`, use the same digamma lower bound at `T`, monotonicity,
`|sin|,|cos|,|sinc|<=1`, and `W(t)>=t^4`. The total correction is bounded by

```
|C(t)|/W(t) <= sum_i 2*w*|a_i|/T^4
              + sum_j |b_j|*T^(j-4).
```

This produces the positive infinite-tail enclosure in the receipt.

## Replay

The committed coefficient list in `certificate.json` is sufficient for
independent replay; it consumes no floating-point LP coefficients.

```sh
python3 -m pip install python-flint==0.9.0
python3 independent_replay.py
```

To repeat discovery and primary certification, also install NumPy/SciPy:

```sh
OPENBLAS_NUM_THREADS=1 python3 regenerate.py
python3 certify.py
python3 independent_replay.py
```

Run from this directory. Discovery may select a different optimum on a
different HiGHS version; certification always checks the actual exact
rounded coefficient list. The committed independent replay is insensitive
to such solver choices.

## Remaining authority boundary

The explicit-symbol inequality is certified. The exact equation identifying
the repository canonical zero quadratic with the angular Fourier integral
of this symbol, together with the genuine-function facts above and a Lean
replay of the interval certificate, must still be proved before claiming
a kernel theorem `Q(g) >= (1/16)*E(g)` on this fixed window. Even that
finite-window theorem would not produce universal Weil positivity or RH.
