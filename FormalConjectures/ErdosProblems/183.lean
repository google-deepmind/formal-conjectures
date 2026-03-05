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
# Erdős Problem 183

Erdős asked whether the limit of R(3;k)^{1/k} exists, where R(3;k) is the multicolor Ramsey
number for triangles — the minimum n such that every k-colouring of the edges of Kₙ contains a
monochromatic triangle.

*Reference:* [erdosproblems.com/183](https://www.erdosproblems.com/183)
-/

open Filter

open scoped Topology

namespace Erdos183

/-- The multicolor Ramsey number $R(3;k)$: the minimum $n$ such that every
$k$-colouring of the edges of $K_n$ contains a monochromatic triangle.
A $k$-colouring is a symmetric function $c : \operatorname{Fin} n \to \operatorname{Fin} n \to \operatorname{Fin} k$,
and a monochromatic triangle is three pairwise distinct vertices
whose three edges all receive the same colour. -/
noncomputable def multicolorRamseyTriangle (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (c : Fin n → Fin n → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a b d : Fin n), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c a b = c a d ∧ c a b = c b d}

/--
Erdős Problem 183 [Er61]:

Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with
$k$ colours then there must exist a monochromatic triangle. The limit
$$\lim_{k \to \infty} R(3;k)^{1/k}$$
exists.

The best upper bound is $R(3;k) \le \lceil e \cdot k! \rceil$, and the best lower bound is
$R(3;k) \ge 380^{k/5} - O(1)$, giving $R(3;k)^{1/k} \ge 380^{1/5} \approx 3.2806$.
-/
@[category research open, AMS 5]
theorem erdos_183 :
    ∃ L : ℝ,
      Tendsto (fun k : ℕ => (multicolorRamseyTriangle k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop (nhds L) := by
  sorry

end Erdos183
