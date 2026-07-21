/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Elliott–Halberstam conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Elliott%E2%80%93Halberstam_conjecture)
- [EH68] Elliott, Peter D. T. A. and Halberstam, Heini, *A conjecture in prime number
  theory*, Symposia Mathematica, Vol. IV (INDAM, Rome, 1968/69), 59–72.
- [FG89] Friedlander, John and Granville, Andrew, *Limitations to the equi-distribution of
  primes I*, Ann. of Math. (2) 129 (1989), no. 2, 363–382.
-/

namespace ElliottHalberstamConjecture

/--
$\pi(x; q, a)$: the number of primes $p \le x$ with $p \equiv a \pmod q$.
-/
def primesInAPCount (x q : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (x + 1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

/--
The error term
$$E(x; q) = \max_{\gcd(a,q)=1} \left|\pi(x;q,a) - \frac{\pi(x)}{\varphi(q)}\right|,$$
measuring the deviation of the primes in the arithmetic progressions modulo $q$ from
uniform distribution among the $\varphi(q)$ coprime residue classes.
-/
noncomputable def E (x q : ℕ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, |(primesInAPCount x q a : ℝ) - (x.primeCounting : ℝ) / (q.totient : ℝ)|

/--
The Elliott–Halberstam conjecture: for every $\theta < 1$ and $A > 0$ there exists a
constant $C > 0$ such that
$$\sum_{1 \le q \le x^{\theta}} E(x; q) \le \frac{C x}{\log^A x}$$
for all $x > 2$.
-/
@[category research open, AMS 11]
theorem elliott_halberstam (θ : ℝ) (hθ : θ < 1) (A : ℝ) (hA : 0 < A) :
    ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A := by
  sorry

/--
The Bombieri–Vinogradov theorem: the Elliott–Halberstam conjecture holds for every
$\theta < 1/2$. This result may be regarded as an averaged form of the generalized
Riemann hypothesis.
-/
@[category research solved, AMS 11]
theorem elliott_halberstam.variants.bombieri_vinogradov (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ)
    (hA : 0 < A) :
    ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A := by
  sorry

/--
The Elliott–Halberstam conjecture fails at the endpoint $\theta = 1$, as shown by
Friedlander and Granville [FG89].
-/
@[category research solved, AMS 11]
theorem elliott_halberstam.variants.friedlander_granville :
    ¬ ∀ A : ℝ, 0 < A → ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 x, E x q ≤ C * x / Real.log x ^ A := by
  sorry

end ElliottHalberstamConjecture
