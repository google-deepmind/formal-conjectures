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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 860

*References:*
- [erdosproblems.com/860](https://www.erdosproblems.com/860)
- [ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to $n$ with distinct
  multiples in another interval*. Nederl. Akad. Wetensch. Indag. Math. 42 (1980), 147-161.
  [PDF](https://www.renyi.hu/~p_erdos/1980-13.pdf)
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. 15
  (1992), 34-50. [PDF](https://hrj.episciences.org/125/pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos860

/-- There are distinct integers $a_1,\ldots,a_{\pi(n)}$ in the open interval $(m,m+L)$ such that
$p_i \mid a_i$ for every $1 \leq i \leq \pi(n)$, where $p_i$ is the $i$th prime. Primes are
indexed from $0$ by `Nat.nth Nat.Prime`, so $p_i$ is `Nat.nth Nat.Prime (i - 1)`. -/
def HasPrimeMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin (Nat.primeCounting n) → ℕ,
    Function.Injective a ∧ ∀ i, m < a i ∧ a i < m + L ∧ Nat.nth Nat.Prime i.val ∣ a i

/-- $h(n)$: the least $L$ such that for every $m \geq 1$ the open interval $(m,m+L)$ contains
distinct integers $a_1,\ldots,a_{\pi(n)}$ with $p_i \mid a_i$, where $p_i$ is the $i$th prime.

The set of such $L$ is nonempty: $L = n\pi(n)+1$ works, since each $p_i \leq n$ has at least
$\pi(n)$ multiples in $(m,m+L)$, so the $a_i$ can be chosen one by one. So `sInf` is the true
minimum. For $n < 2$ there are no primes and $h(n) = 0$. -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {L : ℕ | ∀ m, 1 ≤ m → HasPrimeMultiples n m L}

/-- Any $L$ that works for every $m \geq 1$ is an upper bound for $h(n)$. -/
@[category API, AMS 11]
theorem h_le {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) : h n ≤ L :=
  Nat.sInf_le hL

def erdos_860.answer : ℕ → ℝ := sorry

/--
Let $h(n)$ be such that, for any $m\geq 1$, in the interval $(m,m+h(n))$ there exist distinct
integers $a_i$ for $1\leq i\leq \pi(n)$ such that $p_i\mid a_i$, where $p_i$ denotes the $i$th
prime.

Estimate $h(n)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_860 : (fun n ↦ (h n : ℝ)) =Θ[atTop] erdos_860.answer := by
  sorry

/--
Erdős and Pomerance [ErPo80] proved that
$$h(n) \ll \frac{n^{3/2}}{(\log n)^{1/2}}.$$
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.erdos_pomerance_upper :
    (fun n : ℕ ↦ (h n : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log n) := by
  sorry

/--
Erdős and Selfridge proved $h(n)>(3-o(1))n$.

[ErPo80, (19), p. 159] states this as $\limsup h(n)/n \geq 3$, that is, it holds for infinitely
many $n$. We state that form.
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.erdos_selfridge_lower :
    ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop, (3 - ε) * n ≤ (h n : ℝ) := by
  sorry

/--
Ruzsa proved $h(n)/n\to \infty$, as reported in [Er92c, p. 36].
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.ruzsa :
    Tendsto (fun n : ℕ ↦ (h n : ℝ) / n) atTop atTop := by
  sorry

end Erdos860
