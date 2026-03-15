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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 625

*Reference:* [erdosproblems.com/625](https://www.erdosproblems.com/625)

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either a
complete graph or an empty graph. Let $\chi(G)$ denote the chromatic number.

If $G$ is a random graph with $n$ vertices and each edge included independently with
probability $1/2$, is it true that almost surely
$$\chi(G) - \zeta(G) \to \infty$$
as $n \to \infty$?

[ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory*, 1993.
-/

open SimpleGraph Finset

namespace Erdos625

/-- The simple graph on `Fin n` determined by a Boolean edge matrix. Under $G(n, 1/2)$,
each Boolean matrix is equally likely, so the fraction of matrices whose graph
has a property equals the $G(n, 1/2)$-probability of that property. -/
def toGraph625 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := fun v ⟨h, _⟩ => h rfl

/--
Erdős Problem 625 [ErGi93]:

In the Erdős–Rényi random graph $G(n, 1/2)$ — the uniform distribution over all
labelled simple graphs on $n$ vertices — is it true that the difference
$\chi(G) - \zeta(G)$ tends to infinity almost surely as $n \to \infty$?

Equivalently: for every $M \in \mathbb{N}$ and $\varepsilon > 0$, there exists $n_0$ such
that for all $n \geq n_0$, the fraction of graphs on `Fin n` with
$\chi(G) - \zeta(G) \geq M$ is at least $1 - \varepsilon$.
-/
@[category research open, AMS 5 60]
theorem erdos_625 : answer(sorry) ↔
    ∀ M : ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ((Finset.univ.filter (fun ec : Fin n → Fin n → Bool =>
        χ(toGraph625 ec).toNat - (cochromaticNumber (toGraph625 ec)).toNat ≥ M)).card : ℝ) ≥
      (1 - ε) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) := by
  sorry

end Erdos625
