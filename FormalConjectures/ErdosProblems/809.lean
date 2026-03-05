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
# Erdős Problem 809

*Reference:* [erdosproblems.com/809](https://www.erdosproblems.com/809)

Let $k \geq 3$ and define $F_k(n)$ to be the minimal $r$ such that there is a graph $G$
on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges such that the edges can be $r$-coloured
so that every subgraph isomorphic to $C_{2k+1}$ has no colour repeating on the edges.

Is it true that $F_k(n) \sim n^2/8$?

A problem of Burr, Erdős, Graham, and Sós, who proved that $F_k(n) \gg n^2$.
-/

open SimpleGraph

namespace Erdos809

/-- There exists a graph on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges admitting an
$r$-edge-coloring such that every cycle of length $2k+1$ is rainbow
(no repeated edge colors). -/
noncomputable def AdmitsRainbowOddCycleColoring (k n r : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
    ∃ c : Sym2 (Fin n) → Fin r,
      ∀ (f : Fin (2 * k + 1) → Fin n),
        Function.Injective f →
        (∀ i : Fin (2 * k + 1),
          G.Adj (f i) (f ⟨(i.val + 1) % (2 * k + 1),
            Nat.mod_lt _ (by omega)⟩)) →
        Function.Injective (fun i : Fin (2 * k + 1) =>
          c (Sym2.mk (f i, f ⟨(i.val + 1) % (2 * k + 1),
            Nat.mod_lt _ (by omega)⟩)))

/--
**Erdős Problem 809**: $F_k(n) \sim n^2/8$ for all $k \geq 3$.

For every $\varepsilon > 0$, for sufficiently large $n$, $F_k(n)$ lies between
$(1-\varepsilon)n^2/8$ and $(1+\varepsilon)n^2/8$.
-/
@[category research open, AMS 5]
theorem erdos_809 : answer(sorry) ↔
    ∀ (k : ℕ), k ≥ 3 → ∀ (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (∃ r : ℕ, (↑r : ℝ) ≤ (1 + ε) * ↑n ^ 2 / 8 ∧
          AdmitsRainbowOddCycleColoring k n r) ∧
        (∀ r : ℕ, (↑r : ℝ) < (1 - ε) * ↑n ^ 2 / 8 →
          ¬AdmitsRainbowOddCycleColoring k n r) := by
  sorry

end Erdos809
