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
import FormalConjectures.Wikipedia.HardyLittlewood

/-!
# Erdős Problem 884

*References:*
- [erdosproblems.com/884](https://www.erdosproblems.com/884)
- [Tao25](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf)
-/



namespace Erdos884

noncomputable abbrev sum_inv_of_divisor_pair_differences (n : ℕ) : ℚ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin  j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i )

noncomputable abbrev sum_inv_of_consecutive_divisors (n : ℕ) : ℚ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/--
For a natural number n, let $1 = d_1 < \dotsc < d_{\tau(n)} = n$ denote the divisors of $n$
in increasing order.
Does it hold that
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \ll 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i}$
for $n \to \infty`, i.e.
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \in O \left( 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i}) \right)$?

In September 2025, Terence Tao gave a conditional _negative_ answer to this conjecture,
see `erdos_884_false_of_hardy_littlewood` for this implication.
However, the conjecture itself remains open.
-/
def erdos_884_stmt : Prop :=
    sum_inv_of_divisor_pair_differences ≪ 1 + sum_inv_of_consecutive_divisors

/--
For a natural number n, let $1 = d_1 < \dotsc < d_{\tau(n)} = n$ denote the divisors of $n$
in increasing order.
Does it hold that
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \ll 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i}$
for $n \to \infty`, i.e.
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \in O \left( 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i}) \right)$?

In September 2025, Terence Tao gave a conditional _negative_ answer to this conjecture,
see `erdos_884_false_of_hardy_littlewood` for this implication.
However, the conjecture itself remains open.
-/
@[category research open, AMS 11]
theorem erdos_884 :
    erdos_884_stmt ↔ answer(sorry) := by
  sorry

/--
In September 2025, Terence Tao gave a conditional _negative_ answer to Erdos conjecture 884,
disproving it under the assumption of the *Qualitative Hardy-Littlewood Conjecture*.
See [here](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf).
The *qualitative* version of the conjecture only states that there are infinitely many tuples
of primes and does not require any asymptotical bounds and as such is a corollary of the general
form of the Hardy-Littlewood Conjecture.
We state the 'weaker' implication using general Hardy-Littlewood here, since this conjecture is
already formalized.
-/
@[category research solved, AMS 11]
theorem erdos_884_false_of_hardy_littlewood :
    ∀ (k : ℕ) (m : Fin k.succ → ℕ), HardyLittlewood.FirstHardyLittlewoodConjectureFor m
    → ¬ erdos_884_stmt := by sorry


end Erdos884
