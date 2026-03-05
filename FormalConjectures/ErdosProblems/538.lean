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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 538

*Reference:* [erdosproblems.com/538](https://www.erdosproblems.com/538)

Let $r \geq 2$ and suppose that $A \subseteq \{1, \ldots, N\}$ is such that, for
any $m$, there are at most $r$ solutions to $m = pa$ where $p$ is prime and
$a \in A$. Give the best possible upper bound for $\sum_{n \in A} 1/n$.

Erdős observed that
$$\sum_{n \in A} \frac{1}{n} \sum_{p \leq N} \frac{1}{p}
  \leq r \sum_{m \leq N^2} \frac{1}{m} \ll r \log N,$$
and hence
$$\sum_{n \in A} \frac{1}{n} \ll r \frac{\log N}{\log \log N}.$$

The problem asks whether this bound is the best possible.
-/

open Finset Real

namespace Erdos538

/-- The number of representations of $m$ as $p \cdot a$ where $p$ is prime and
$a \in A$. Since $p$ is determined by $a$ (as $p = m / a$), this counts
elements $a \in A$ with $a \mid m$ and $m / a$ prime. -/
def numPrimeProductReps (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => a ∣ m ∧ Nat.Prime (m / a))).card

/--
**Erdős Problem 538** (Sharpness conjecture):

The upper bound is best possible: there exists $c > 0$ such that for all
$r \geq 2$ and sufficiently large $N$, there exists $A \subseteq \{1, \ldots, N\}$ satisfying
the representation constraint with
$$\sum_{n \in A} \frac{1}{n} \geq c \cdot r \cdot \frac{\log N}{\log \log N}.$$
-/
@[category research open, AMS 11]
theorem erdos_538 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ r : ℕ, 2 ≤ r →
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ m : ℕ, numPrimeProductReps A m ≤ r) ∧
        c * (r : ℝ) * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ≤
          A.sum (fun n => (1 : ℝ) / (n : ℝ)) := by
  sorry

/--
**Erdős Problem 538** (Erdős's upper bound):

There exists a constant $C > 0$ such that for all $r \geq 2$ and sufficiently
large $N$, if $A \subseteq \{1, \ldots, N\}$ has at most $r$ representations $m = p \cdot a$
(with $p$ prime and $a \in A$) for every $m$, then
$$\sum_{n \in A} \frac{1}{n} \leq C \cdot r \cdot \frac{\log N}{\log \log N}.$$
-/
@[category research solved, AMS 11]
theorem erdos_538.variants.upper_bound :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ r : ℕ, 2 ≤ r →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N →
        (∀ m : ℕ, numPrimeProductReps A m ≤ r) →
        A.sum (fun n => (1 : ℝ) / (n : ℝ)) ≤
          C * (r : ℝ) * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) := by
  sorry

end Erdos538
