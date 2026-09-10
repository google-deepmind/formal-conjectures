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

import FormalConjecturesUtil

/-!
# Erdős Problem 161

*References:*
- [erdosproblems.com/161](https://www.erdosproblems.com/161)
- [CFS11] Conlon, David and Fox, Jacob and Sudakov, Benny, Large almost monochromatic subsets in
  hypergraphs. Israel J. Math. (2011), 423--432.
- [Er90b] Erdős, Paul, Problems and results on graphs and hypergraphs: similarities and differences
  . Mathematics of Ramsey theory (1990), 12-28.
-/

namespace Erdos161

open Filter Asymptotics

/--
Let $\alpha\in[0,1/2)$ and $n,t\geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that we can
$2$-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that if $X\subseteq
[n]$ with $\lvert X\rvert \geq m$ then there are at least $\alpha \binom{\lvert X\rvert}{t}$ many
$t$-subsets of $X$ of each colour. For fixed $n,t$ as we change $\alpha$ from $0$ to $1/2$ does
$F^{(t)}(n,\alpha)$ increase continuously or are there jumps? Only one jump?

Here growth is compared up to constant factors as $n\to\infty$. At $\alpha=0$,
each color must occur, following the source's Ramsey convention.
-/
@[category research open, AMS 5]
theorem erdos_161.parts.i :
    let E : ℕ → Set (ℝ × ℝ) := answer(sorry)
    ∀ t : ℕ, 1 ≤ t →
      {p | p.1 ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ p.2 ∈ Set.Ico (0 : ℝ) (1 / 2) ∧
        (fun n ↦ (Hypergraph.balancedColoringThreshold n t p.1 : ℝ)) =Θ[atTop]
          (fun n ↦ (Hypergraph.balancedColoringThreshold n t p.2 : ℝ))} = E t := by
  sorry

/--
For fixed $t\geq 3$, do all positive densities below $1/2$ give the same asymptotic order?
-/
@[category research open, AMS 5]
theorem erdos_161.parts.ii :
    answer(sorry) ↔ ∀ t : ℕ, 3 ≤ t → ∀ α β : ℝ,
    0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
    (fun n ↦ (Hypergraph.balancedColoringThreshold n t α : ℝ)) =Θ[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n t β : ℝ)) := by
  sorry

end Erdos161
