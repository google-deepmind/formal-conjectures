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
# Erdős Problem 287

*Reference:* [erdosproblems.com/287](https://www.erdosproblems.com/287)

Is it true that any Egyptian fraction representation of 1 with distinct denominators greater
than 1 must have a consecutive gap of at least 3?

[Er32] Erdős, P., _Egyszerű bizonyítás Kürschák egy tételére_ (1932).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Va99] §1.15.
-/

namespace Erdos287

/--
Erdős Problem 287 [ErGr80, p.33]:

Let $k \geq 2$. Is it true that, for any distinct integers $1 < n_1 < \cdots < n_k$ such that
$1 = 1/n_1 + \cdots + 1/n_k$, we must have $\max(n_{i+1} - n_i) \geq 3$?

The example $1 = 1/2 + 1/3 + 1/6$ shows that $3$ would be best possible here.
The lower bound of $\geq 2$ is equivalent to saying that $1$ is not the sum of
reciprocals of consecutive integers, proved by Erdős [Er32].
-/
@[category research open, AMS 11]
theorem erdos_287 : answer(sorry) ↔
    ∀ (S : Finset ℕ),
      2 ≤ S.card →
      (∀ n ∈ S, 1 < n) →
      S.sum (fun n => (1 : ℚ) / ↑n) = 1 →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ c ∈ S, c ≤ a ∨ b ≤ c) /- a, b consecutive in S -/
        ∧ 3 ≤ b - a := by
  sorry

end Erdos287
