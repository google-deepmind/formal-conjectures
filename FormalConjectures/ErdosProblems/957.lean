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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 957

*References:*
- [erdosproblems.com/957](https://www.erdosproblems.com/957)
- [Du19] Dumitrescu, Adrian, *A product inequality for extreme distances*.
  Comput. Geom. 85 (2019), 101577.
  [PDF](https://adriandumitrescu.org/product-ineq.pdf)
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica 10 (1990), 261-269.
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos957

set_option linter.style.formal_proof_palomar false in
/--
Let $A\subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1<\ldots<d_k\}$ be the set of
distinct distances determined by $A$. Let $f(d)$ be the number of times the distance $d$ is
determined. Is it true that
$$f(d_1)f(d_k) \leq (\tfrac{9}{8}+o(1))n^2?$$

A question of Erdős and Pach [ErPa90]. The answer is yes, proved by Dumitrescu [Du19]. Here
$f(d)$ counts unordered pairs of points of $A$ at distance $d$ (`distanceMultiplicity`), and
$o(1)$ is uniform over all $A$ of size $n$.
-/
@[category research solved, question, AMS 5 52, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos957.lean#L57"]
theorem erdos_957 :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card = n →
      ∀ d₁ dₖ : ℝ, IsLeast (distanceSet A : Set ℝ) d₁ →
        IsGreatest (distanceSet A : Set ℝ) dₖ →
          (distanceMultiplicity A d₁ : ℝ) * distanceMultiplicity A dₖ ≤
            (9 / 8 + ε) * (n : ℝ) ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The original problem was solved by Dumitrescu [Du19, Theorem 1], who proved that
$$f(d_1)f(d_k)\leq \frac{9}{8}n^2+O(n).$$
Here a single constant $C$ in the error term $Cn$ works for all finite $A \subset \mathbb{R}^2$.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos957.lean#L44"]
theorem erdos_957.variants.dumitrescu :
    ∃ C : ℝ, ∀ A : Finset ℝ², ∀ d₁ dₖ : ℝ, IsLeast (distanceSet A : Set ℝ) d₁ →
      IsGreatest (distanceSet A : Set ℝ) dₖ →
        (distanceMultiplicity A d₁ : ℝ) * distanceMultiplicity A dₖ ≤
          9 / 8 * (A.card : ℝ) ^ 2 + C * (A.card : ℝ) := by
  sorry

end Erdos957
