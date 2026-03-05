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
# Erdős Problem 648

*Reference:* [erdosproblems.com/648](https://www.erdosproblems.com/648)

Let $g(n)$ denote the largest $t$ such that there exist integers
$2 \leq a_1 < a_2 < \cdots < a_t < n$ such that
$P(a_1) > P(a_2) > \cdots > P(a_t)$,
where $P(m)$ is the greatest prime factor of $m$. Estimate $g(n)$.

Stijn Cambie proved that $g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}$.
Cambie further asks whether there exists a constant $c$ such that
$g(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}$, and shows that such $c$
must satisfy $2 \leq c \leq 2\sqrt{2}$.

[Ca25b] Cambie, S., _Longest decreasing sequences of largest prime factors_.
-/

open Real

namespace Erdos648

/-- The greatest prime factor of $n$, or $0$ if $n \leq 1$. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/-- $g(n)$ is the largest $t$ such that there exist integers $2 \leq a_1 < a_2 < \cdots < a_t < n$
with $P(a_1) > P(a_2) > \cdots > P(a_t)$, where $P(m)$ is the greatest prime factor. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ a : Fin t → ℕ,
    (∀ i, 2 ≤ a i ∧ a i < n) ∧
    StrictMono a ∧
    StrictAnti (fun i => greatestPrimeFactor (a i))}

/--
Erdős Problem 648 (proved by Cambie [Ca25b]):

$g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}$, i.e., there exist positive
constants $c_1, c_2$ such that for all sufficiently large $n$,
$$c_1 \sqrt{\frac{n}{\log n}} \leq g(n) \leq c_2 \sqrt{\frac{n}{\log n}}.$$
-/
@[category research solved, AMS 11]
theorem erdos_648 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ (g n : ℝ) ∧
      (g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) := by
  sorry

end Erdos648
