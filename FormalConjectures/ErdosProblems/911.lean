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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 911

Is there a function $f$ with $f(x)/x \to \infty$ such that, for all sufficiently large $C$,
every graph $G$ with $n$ vertices and at least $Cn$ edges satisfies
$\hat{R}(G) > f(C) \cdot |E(G)|$?

*Reference:* [erdosproblems.com/911](https://www.erdosproblems.com/911)

[Er82e] Erdős, P., _Problems and results in graph theory_. (1982), p. 78.
-/

open SimpleGraph

namespace Erdos911

/--
Erdős Problem #911 [Er82e, p.78]:

Is there a function $f : \mathbb{N} \to \mathbb{N}$ with $f(x)/x \to \infty$ as
$x \to \infty$ such that, for all sufficiently large $C$, if $G$ is any graph with
$n$ vertices and at least $C \cdot n$ edges then
$\hat{R}(G) > f(C) \cdot |E(G)|$?
-/
@[category research open, AMS 5]
theorem erdos_911 :
    answer(sorry) ↔
    ∃ f : ℕ → ℕ,
      -- f(x)/x → ∞ as x → ∞
      (∀ M : ℕ, ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ → f x ≥ M * x) ∧
      -- For all large C, the bound holds
      ∃ C₀ : ℕ, ∀ C : ℕ, C ≥ C₀ →
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          G.edgeSet.ncard ≥ C * n →
          sizeRamsey G G > f C * G.edgeSet.ncard := by
  sorry

end Erdos911
