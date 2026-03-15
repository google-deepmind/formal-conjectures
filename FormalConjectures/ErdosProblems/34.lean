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
# Erdős Problem 34

*Reference:* [erdosproblems.com/34](https://www.erdosproblems.com/34)

For a permutation $\pi$ of $\{1,\ldots,n\}$, let $S(\pi)$ count the distinct consecutive sums.
Is $S(\pi) = o(n^2)$ for all $\pi$? Disproved by Hegyvári [He86]; Konieczny [Ko15] showed
a random permutation has $\sim \frac{1+e^{-2}}{4} \cdot n^2$ distinct consecutive sums.

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.

[ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique **28** (1980).

[He86] Hegyvári, N., _On consecutive sums in sequences_. Acta Math. Hungar. (1986), 193–200.

[Ko15] Konieczny, J., _On consecutive sums in permutations_. arXiv:1504.07156 (2015).
-/

open Finset BigOperators Equiv

namespace Erdos34

/--
For a permutation $\sigma$ of $\operatorname{Fin}(n)$, the set of distinct consecutive sums.
A consecutive sum is $\sum_{i \in [u,v]} (\sigma(i) + 1)$ for $u \leq v$ in $\operatorname{Fin}(n)$,
corresponding to summing consecutive values of a permutation of $\{1,\ldots,n\}$.
-/
noncomputable def consecutiveSums (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  ((Finset.univ (α := Fin n)) ×ˢ (Finset.univ (α := Fin n))).filter (fun p => p.1 ≤ p.2)
    |>.image (fun p => ∑ i ∈ Finset.Icc p.1 p.2, ((σ i).val + 1))

/--
For a permutation $\pi$ of $\{1,\ldots,n\}$, let $S(\pi)$ count the number of distinct
consecutive sums (sums of the form $\sum_{u \leq i \leq v} \pi(i)$).
Is it true that $S(\pi) = o(n^2)$ for all $\pi \in S_n$?

This was disproved by Hegyvári [He86] and shown to be extremely false by
Konieczny [Ko15], who proved that a random permutation has
$\sim \frac{1+e^{-2}}{4} \cdot n^2$ distinct consecutive sums.
-/
@[category research solved, AMS 5]
theorem erdos_34 : answer(False) ↔
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ σ : Equiv.Perm (Fin n),
          ((consecutiveSums n σ).card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos34
