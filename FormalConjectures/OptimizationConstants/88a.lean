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
# Tao's Optimization Constant 88a / Bounded prime gap constant

*References:*
- [Tao's constant 88a](https://teorth.github.io/optimizationproblems/constants/88a.html)
- [Zha14] Zhang, Y., *Bounded gaps between primes*.
  Ann. of Math. **179** (2014), 1121–1174.
  [DOI](https://doi.org/10.4007/annals.2014.179.3.7)
- [May15] Maynard, J., *Small gaps between primes*.
  Ann. of Math. **181** (2015), 383–413.
  [DOI](https://doi.org/10.4007/annals.2015.181.1.7)
- [Pol14b] D. H. J. Polymath, *Variants of the Selberg sieve, and bounded intervals
  containing many primes*. Res. Math. Sci. **1** (2014), Article 12; erratum **2** (2015),
  Article 15. [arXiv](https://arxiv.org/abs/1407.4897)
- [Sta26] Stadlmann, J., *Bounded gaps between primes* (2026).
  [arXiv](https://arxiv.org/abs/2608.31126)
- [OAI26] OpenAI, *Improved short gaps between primes*. Preprint, 30 August 2026.
  [PDF](https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/short_gaps.pdf)
-/

namespace Constant88a

open Nat Finset

/-- **Tao's Optimization Constant 88a / Bounded prime gap constant**.
The lower limit of consecutive prime gaps. -/
noncomputable def C88a : ℕ :=
  sInf {k | k ≠ 0 ∧ {p : ℕ | p.Prime ∧ (p + k).Prime}.Infinite}

/-- C88a = 2 is equivalent to the twin prime conjecture. -/
@[category API, AMS 11]
theorem c88a_two_iff_twin_prime : C88a = 2 ↔ {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by
  sorry

/-- The first and current best known lower bound is $2$. -/
@[category textbook, AMS 11]
theorem c88a_lower_bound : 2 ≤ C88a := by
  sorry

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 11]
theorem c88a_lower_bound_improved : answer(sorry) ↔ 2 < C88a := by
  sorry

/-- The number of primes at most $x$ in the residue class $a$ modulo $q$. -/
noncomputable def primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

local notation "π(" x "; " q ", " a ")" => primeCountingZMod x q a
local notation "π(" x ")" => Nat.primeCounting ⌊x⌋₊

/-- The Bombieri–Vinogradov theorem gives the prime-counting discrepancy estimate for
every exponent $\theta < 1/2$ [May15, Equation (1.3)]. -/
@[category research solved, AMS 11]
theorem bombieri_vinogradov :
    ∀ θ < (1 / 2 : ℝ), ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
      ∑ q ∈ Icc (1 : ℕ) ⌊x ^ θ⌋₊,
        ⨆ a : (ZMod q)ˣ, |(π(x; q, a) - π(x) / φ q : ℝ)| ≤ c * x / x.log ^ A := by
  sorry

/-- The first known upper bound is $70000000$. Zhang proves equidistribution beyond the
Bombieri–Vinogradov range for smooth moduli [Zha14]. -/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/AxiomMath/PrimeGapsLib/commit/cddbc9291641545da52f06392c8ef46e1d6c6b7c"
  assuming bombieri_vinogradov]
theorem c88a_le_70000000 : C88a ≤ 70000000 := by
  sorry

/-- Maynard's multidimensional Selberg sieve gives $C_{88a} \le 600$, using the
Bombieri–Vinogradov theorem [May15]. -/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/AxiomMath/PrimeGapsLib/commit/cddbc9291641545da52f06392c8ef46e1d6c6b7c"
  assuming bombieri_vinogradov]
theorem c88a_le_600 : C88a ≤ 600 := by
  sorry

/-- Polymath8b obtains $C_{88a} \le 246$ by refining the multidimensional Selberg sieve
and its numerical optimization [Pol14b, Theorem 1.4(i)]. -/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/AxiomMath/PrimeGapsLib/commit/cddbc9291641545da52f06392c8ef46e1d6c6b7c"
  assuming bombieri_vinogradov]
theorem c88a_le_246 : C88a ≤ 246 := by
  sorry

/-- Stadlmann obtains $C_{88a} \le 240$ by combining Bombieri–Vinogradov
with improved equidistribution estimates for smooth moduli [Sta26]. -/
@[category research solved, AMS 11]
theorem c88a_le_240 : C88a ≤ 240 := by
  sorry

/--
The current best known upper bound is $186$. OpenAI proves $\mathrm{DHL}[40,2]$
and applies it to an admissible $40$-tuple of diameter $186$ [OAI26, Corollary 1.2].

OpenAI's Lean formalization is conditional on two published exponential-sum estimates
and numerical integral and cap bounds.
-/
@[category research solved, AMS 11]
theorem c88a_upper_bound : C88a ≤ 186 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 11]
theorem c88a_upper_bound_improved : answer(sorry) ↔ C88a < 186 := by
  sorry

end Constant88a
