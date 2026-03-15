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
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Erdős Problem 795

*Reference:* [erdosproblems.com/795](https://www.erdosproblems.com/795)

*Related:* [Erdős Problem 786](https://www.erdosproblems.com/786)

Let $g(n)$ be the maximal size of $A \subseteq \{1, \ldots, n\}$ such that the subset products
$\prod_{a \in S} a$ are distinct for all $S \subseteq A$. Erdős [Er66] proved that
$g(n) \leq \pi(n) + O(\sqrt{n} / \log n)$. This upper bound is essentially best possible,
since one could take $A$ to be all primes and squares of primes.

Raghavan [Ra25] resolved this, proving
$g(n) \leq \pi(n) + \pi(\lfloor\sqrt{n}\rfloor) + O(n^{5/12 + o(1)})$ and also
$g(n) \geq \pi(n) + \pi(\lfloor\sqrt{n}\rfloor) + \pi(n^{1/3})/3 - O(1)$.

[Er66] Erdős, P., _Remarks on number theory. V. Extremal problems in number theory. II_.
Mat. Lapok (1966), 135–155.

[Ra25] Raghavan, S., _Sharp bounds for sets with distinct subset products_.
arXiv:2501.02695 (2025).
-/

open Finset BigOperators

namespace Erdos795

/-- A finset of natural numbers has distinct subset products if for all subsets
$S, T \subseteq A$, $\prod_{a \in S} a = \prod_{a \in T} a$ implies $S = T$. -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  ∀ S T, S ⊆ A → T ⊆ A → (∏ i ∈ S, i) = (∏ i ∈ T, i) → S = T

/-- $g(n)$: the maximal cardinality of $A \subseteq \{1, \ldots, n\}$ with distinct subset
products. -/
noncomputable def maxDistinctProductSetSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    HasDistinctSubsetProducts A ∧ A.card = k}

/--
Erdős Problem 795: $g(n) \leq \pi(n) + \pi(\lfloor\sqrt{n}\rfloor) + o(\sqrt{n} / \log n)$.

Formulated as: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$,
$g(n) \leq \pi(n) + \pi(\lfloor\sqrt{n}\rfloor) + \varepsilon \cdot \sqrt{n} / \log n$.

This was solved by Raghavan [Ra25], who proved
$g(n) \leq \pi(n) + \pi(\lfloor\sqrt{n}\rfloor) + O(n^{5/12 + o(1)})$.
-/
@[category research solved, AMS 5 11]
theorem erdos_795 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxDistinctProductSetSize n : ℝ) ≤
        (Nat.primeCounting n : ℝ) + (Nat.primeCounting (Nat.sqrt n) : ℝ) +
        ε * (Nat.sqrt n : ℝ) / Real.log (n : ℝ) := by
  sorry

end Erdos795
