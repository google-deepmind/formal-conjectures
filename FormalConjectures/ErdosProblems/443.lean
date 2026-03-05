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
# Erdős Problem 443

*Reference:* [erdosproblems.com/443](https://www.erdosproblems.com/443)

Let $m,n\geq 1$. What is
$$\# \{ k(m-k) : 1\leq k\leq m/2\} \cap \{ l(n-l) : 1\leq l\leq n/2\}?$$
Can it be arbitrarily large? Is it $\leq (mn)^{o(1)}$ for all sufficiently
large $m,n$?

This was solved independently by Hegyvári [He25] and Cambie (unpublished), who
show that if $m > n$ then the set in question has size
$\leq m^{O(1/\log\log m)}$, and that for any integer $s$ there exist infinitely
many pairs $(m,n)$ such that the set in question has size $s$.

[He25] Hegyvári, N., _On a problem of Erdős on integers which are simultaneously
of the form $ab$ and $(a+k)(b+k)$_ (2025).
-/

open Finset Real

namespace Erdos443

/-- The set $\{k(m-k) : 1 \leq k \leq m/2\}$ of products arising from partitioning $m$
into two positive parts $k$ and $m-k$ with $k \leq m/2$. -/
def productSet (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (m / 2)).image (fun k => k * (m - k))

/-- The number of common values in the product sets for $m$ and $n$. -/
def commonProducts (m n : ℕ) : ℕ :=
  ((productSet m) ∩ (productSet n)).card

/-- Erdős Problem 443, part 1:
The intersection can be arbitrarily large. For any $s$, there exist
arbitrarily large $m$ and some $n \geq 1$ with
$|\operatorname{productSet}(m) \cap \operatorname{productSet}(n)| \geq s$.

Proved independently by Hegyvári [He25] and Cambie (unpublished). -/
@[category research solved, AMS 5 11]
theorem erdos_443 (s : ℕ) :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∃ n : ℕ, 1 ≤ n ∧ s ≤ commonProducts m n := by
  sorry

/-- Erdős Problem 443, part 2:
If $m > n$ then the intersection has subpolynomial size:
$|\operatorname{productSet}(m) \cap \operatorname{productSet}(n)| \leq m^{C / \log \log m}$
for some constant $C > 0$ and all sufficiently large $m$.

Proved independently by Hegyvári [He25] and Cambie (unpublished). -/
@[category research solved, AMS 5 11]
theorem erdos_443.variants.upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∀ n : ℕ, 1 ≤ n → n < m →
    (commonProducts m n : ℝ) ≤ (m : ℝ) ^ (C / Real.log (Real.log (m : ℝ))) := by
  sorry

end Erdos443
