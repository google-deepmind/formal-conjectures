/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 647

*Reference:* [erdosproblems.com/647](https://www.erdosproblems.com/647)
-/

namespace Erdos647

open Filter ArithmeticFunction.sigma

/-- Let $\tau(n)$ count the number of divisors of $n$. Is there some $n > 24$ such that
$$
  \max_{m < n}(m + \tau(m)) \leq n + 2?
$$ -/
@[category research open, AMS 11]
theorem erdos_647 : answer(sorry) ↔ ∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2 := by
  sorry

/-- This is true for $n = 24$. -/
@[category research solved, AMS 11]
theorem erdos_647.variants.twenty_four : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

/-- Erdős says 'it is extremely doubtful' that there are infinitely many such $n$, and in
fact suggests that
$$
  lim_{n\to\infty} \max_{m < n}(\tau(m) + m − n) = \infty.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.lim :
    answer(sorry) ↔ atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop := by
  sorry

/-- Erdős says it 'seems certain' that for every $k$ there are infinitely many $n$
for which
$$
  \max_{n−k < m < n}(m + \tau(m)) ≤ n + 2.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.infinite :
    answer(sorry) ↔ ∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite := by
  sorry

/-- **Modular ladder, partial progress.**
Any $n > 54$ satisfying the $(\ast)$-condition of `erdos_647` must be divisible by
$840 = 2^3 \cdot 3 \cdot 5 \cdot 7$. This re-derives in Lean the elementary modular
chain of T. Tao (Oct 2025 forum) up through $7 \mid n$, including Boris Alexeev's
mod-8 sharpening (Jan 2026) as a separate proved lemma. The asymptotic closure
of `erdos_647` itself (essentially Schinzel's hypothesis H for the relevant
tuple) is out of scope. The full Lean development (25 proved lemmas, 12
`sorry`-stubbed follow-up targets covering $9, 11, 13 \mid n$ and the Phase-2
prime/near-prime conditions on $N$) is hosted at the link below. -/
@[category research solved, AMS 11, formal_proof using lean4 at
"https://gist.github.com/alejandrozarco/a2a94d6150e8667d19a8f2b3ec3ed3a0#file-erdos647modular-lean"]
theorem erdos_647.variants.dvd_840 :
    ∀ n > 54, (⨆ m : Fin n, (m : ℕ) + σ 0 m) ≤ n + 2 → 840 ∣ n := by
  sorry

end Erdos647
