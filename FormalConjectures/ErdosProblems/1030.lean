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
# Erdős Problem 1030

*Reference:* [erdosproblems.com/1030](https://www.erdosproblems.com/1030)

If $R(k,l)$ is the Ramsey number then prove the existence of some $c > 0$ such that
$$
  \lim_{k \to \infty} \frac{R(k+1, k)}{R(k, k)} > 1 + c.
$$

A problem of Erdős and Sós, who could not even prove whether
$R(k+1,k) - R(k,k) > k^c$ for any $c > 1$.

[Er93] Erdős, P., _On some of my favourite theorems_ (1993), p. 339.
-/

open SimpleGraph

namespace Erdos1030

/-- The Ramsey number $R(k, l)$: the minimum $N$ such that every simple graph on $N$
    vertices contains either a $k$-clique or an independent set of size $l$
    (equivalently, an $l$-clique in the complement). -/
noncomputable def ramseyR (k l : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree l}

/--
Erdős Problem 1030 [Er93, p. 339]:

There exists $c > 0$ such that
$$
  \lim_{k \to \infty} \frac{R(k+1, k)}{R(k, k)} > 1 + c.
$$

Formulated as: there exist $c > 0$ and $K_0$ such that for all $k \geq K_0$,
$R(k+1, k) / R(k, k) \geq 1 + c$.
-/
@[category research open, AMS 5]
theorem erdos_1030 :
    ∃ c : ℝ, c > 0 ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (ramseyR (k + 1) k : ℝ) / (ramseyR k k : ℝ) ≥ 1 + c := by
  sorry

end Erdos1030
