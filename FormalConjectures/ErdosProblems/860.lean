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
# Erdős Problem 860

*References:*
- [erdosproblems.com/860](https://www.erdosproblems.com/860)
- [ErPo80] P. Erdős and C. Pomerance, *Matching the natural numbers up to $n$ with distinct
  multiples of another interval*. Indagationes Math. (1980), 147-151.
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. (1992),
  34-50.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

open Asymptotics Filter
open scoped Nat.Prime

namespace Erdos860

/--
`h n` is the least `t` such that, for every `m ≥ 1`, the open interval `(m, m + t)` contains
distinct integers `a i` with `pᵢ ∣ a i` for each of the first `π n` primes.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {t : ℕ | ∀ m ≥ 1, ∃ a : Fin (π n) → ℕ, a.Injective ∧
    ∀ i, a i ∈ Set.Ioo m (m + t) ∧ (i : ℕ).nth Nat.Prime ∣ a i}

/--
Let $h(n)$ be such that, for any $m\geq 1$, in the interval $(m,m+h(n))$ there exist distinct
integers $a_i$ for $1\leq i\leq \pi(n)$ such that $p_i\mid a_i$, where $p_i$ denotes the $i$th
prime.

Estimate $h(n)$.
-/
@[category research open, AMS 11]
theorem erdos_860 :
    let g : ℕ → ℝ := answer(sorry)
    (fun n => (h n : ℝ)) ~[atTop] g := by
  sorry

/--
A problem of Erdős and Pomerance [ErPo80], who proved
$$h(n) \ll \frac{n^{3/2}}{(\log n)^{1/2}}.$$
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.erdos_pomerance :
    (fun n => (h n : ℝ)) ≪
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) / (Real.log n) ^ (1 / 2 : ℝ) := by
  sorry

/--
Erdős and Selfridge proved $h(n)>(3-o(1))n$.
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.erdos_selfridge :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (3 - ε) * (n : ℝ) < (h n : ℝ) := by
  sorry

/--
Ruzsa proved $h(n)/n\to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.ruzsa :
    Tendsto (fun n => (h n : ℝ) / n) atTop atTop := by
  sorry

end Erdos860
