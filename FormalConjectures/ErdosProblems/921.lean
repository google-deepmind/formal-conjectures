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
# Erdős Problem 921

*References:*
- [erdosproblems.com/921](https://www.erdosproblems.com/921)
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Ga63] Gallai, T., Kritische Graphen. I. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1963), 165-192.
- [KST84] Kierstead, H. A., Szemerédi, E. and Trotter, W. T., On coloring graphs with locally
  small chromatic number. Combinatorica (1984), 183-185.
-/

open Filter

namespace Erdos921

/--
Let $k\geq 4$ and let $f_k(n)$ be the largest $m$ such that there is a graph on $n$ vertices
with chromatic number $k$ in which every odd cycle has length $> m$.
Then
$$f_k(n) \asymp n^{\frac{1}{k-2}}.$$

A question of Erdős and Gallai.

Proved for all $k\geq 4$ by Kierstead, Szemerédi, and Trotter [KST84].
-/
@[category research solved, AMS 5]
theorem erdos_921 : answer(True) ↔
    ∀ (k : ℕ), 4 ≤ k →
      ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
        (∀ᶠ (n : ℕ) in atTop,
          (∃ (G : SimpleGraph (Fin n)),
            G.chromaticNumber = (k : ℕ∞) ∧
            ∀ l ∈ G.oddCycleLengths, c₁ * (n : ℝ) ^ (1 / ((k : ℝ) - 2)) < (l : ℝ))) ∧
        (∀ᶠ (n : ℕ) in atTop,
          ∀ (G : SimpleGraph (Fin n)),
            G.chromaticNumber = (k : ℕ∞) →
            ∃ l ∈ G.oddCycleLengths, (l : ℝ) ≤ c₂ * (n : ℝ) ^ (1 / ((k : ℝ) - 2))) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos921
