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
# Erdős Problem 702

*Reference:* [erdosproblems.com/702](https://www.erdosproblems.com/702)

If a family of k-element subsets of {1,...,n} has more than C(n-2,k-2) members (where k ≥ 4),
then some two members of the family intersect in exactly one element.

See also: Problem 703.

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 108.
[Er76b] Erdős, P., _Problems in combinatorial and graph theory_ (1976), p. 186.
[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_, 1981.
[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_, 1982.
[Fr77] Frankl, P., *On families of finite sets no two of which intersect in a singleton*,
Bull. Austral. Math. Soc. 17 (1977), 125–134.
-/

open Finset

namespace Erdos702

/--
**Erdős–Sós Conjecture.** Let $k \geq 4$. If $\mathcal{F}$ is a family of $k$-element subsets of
$\{1, \ldots, n\}$ with $|\mathcal{F}| > \binom{n-2}{k-2}$, then there exist distinct
$A, B \in \mathcal{F}$ such that $|A \cap B| = 1$.

Proved by Katona (unpublished) for $k = 4$, and by Frankl [Fr77] for all $k \geq 4$.
-/
@[category research solved, AMS 5]
theorem erdos_702 (n k : ℕ) (hk : 4 ≤ k) (h2k : 2 * k - 1 ≤ n)
    (F : Finset (Finset (Fin n)))
    (hF_unif : ∀ A ∈ F, A.card = k)
    (hF_large : F.card > Nat.choose (n - 2) (k - 2)) :
    ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ (A ∩ B).card = 1 := by
  sorry

end Erdos702
