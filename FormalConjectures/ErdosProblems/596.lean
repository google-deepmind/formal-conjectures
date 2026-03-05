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
# Erdős Problem 596

*Reference:* [erdosproblems.com/596](https://www.erdosproblems.com/596)

For which graphs $G_1$, $G_2$ is it true that for every $n \geq 1$ there is a $G_1$-free
graph $H$ such that every $n$-coloring of the edges of $H$ contains a monochromatic copy
of $G_2$, and yet for every $G_1$-free graph $H$ there is an $\aleph_0$-coloring of the
edges of $H$ without a monochromatic $G_2$?

Erdős and Hajnal originally conjectured that no such $G_1$, $G_2$ exist, but $G_1 = C_4$
and $G_2 = C_6$ is an example (Nešetřil–Rödl for the finite Ramsey property, Erdős–Hajnal
for the countable case). Whether $G_1 = K_4$, $G_2 = K_3$ works is problem 595.

[Er87] Erdős, P., _Some problems and results in combinatorial number theory_ (1987).
-/

open SimpleGraph

namespace Erdos596

/-- A graph $H$ contains a monochromatic copy of $G$ under edge coloring $c$: there exists
an embedding of $G$ into $H$ such that all edges in the image receive the same color. -/
def HasMonochromaticCopy {W : Type*} {V : Type*}
    (H : SimpleGraph V) (G : SimpleGraph W) {α : Type*} (c : V → V → α) : Prop :=
  ∃ (φ : G ↪g H) (color : α), ∀ u v, G.Adj u v → c (φ u) (φ v) = color

/--
Erdős Problem 596 [Er87]:

There exist finite graphs $G_1$ and $G_2$ such that:
(a) For every $n \geq 1$, there exists a $G_1$-free graph $H$ such that every $n$-coloring
    of $H$'s edges contains a monochromatic copy of $G_2$.
(b) For every $G_1$-free graph $H$, there exists a countable coloring of $H$'s edges
    with no monochromatic copy of $G_2$.

The known example is $G_1 = C_4$, $G_2 = C_6$ (Nešetřil–Rödl for the finite Ramsey
property, Erdős–Hajnal for the countable case). The full characterization of
all such pairs remains open.
-/
@[category research solved, AMS 5]
theorem erdos_596 :
    ∃ (W₁ : Type) (G₁ : SimpleGraph W₁) (W₂ : Type) (G₂ : SimpleGraph W₂),
      -- (a) Finite Ramsey property: for every n ≥ 1, there exists a G₁-free graph
      -- whose edges cannot be n-colored without a monochromatic G₂
      (∀ n : ℕ, 1 ≤ n →
        ∃ (V : Type) (H : SimpleGraph V),
          IsEmpty (G₁ ↪g H) ∧
          ∀ c : V → V → Fin n, HasMonochromaticCopy H G₂ c) ∧
      -- (b) Countable failure: every G₁-free graph can be countably colored
      -- without a monochromatic G₂
      (∀ (V : Type) (H : SimpleGraph V),
        IsEmpty (G₁ ↪g H) →
        ∃ c : V → V → ℕ, ¬HasMonochromaticCopy H G₂ c) := by
  sorry

end Erdos596
