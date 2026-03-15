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
# Erdős Problem 974

*Reference:* [erdosproblems.com/974](https://www.erdosproblems.com/974)

A conjecture of Turán [Er65b, p.213], proved by Tijdeman [Ti66].

[Er65b] Erdős, P., _Extremal problems in number theory_ (1965), p.213.
[Ti66] Tijdeman, R., _On a conjecture of Turán and Erdős_. Indag. Math. (1966), 374–383.
-/

open Finset BigOperators Complex

namespace Erdos974

/--
Erdős Problem 974 (Turán's conjecture, proved by Tijdeman [Ti66]):

If $z : \text{Fin}\; n \to \mathbb{C}$ with $z_0 = 1$, and there are infinitely many $k \in \mathbb{N}$
such that the $n - 1$ consecutive power sums $s_k, s_{k+1}, \ldots, s_{k+n-2}$ are all zero,
then the $z_i$ are a permutation of the $n$-th roots of unity $e^{2\pi i j/n}$.
-/
@[category research solved, AMS 11 30]
theorem erdos_974 {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ)
    (hz1 : z ⟨0, by omega⟩ = 1)
    (hzeros : ∀ N : ℕ, ∃ k ≥ N, ∀ j : ℕ, j < n - 1 →
      (∑ i : Fin n, (z i) ^ (k + j)) = 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
      z (σ i) = exp (2 * ↑Real.pi * I * ↑(i.val) / ↑n) := by
  sorry

end Erdos974
