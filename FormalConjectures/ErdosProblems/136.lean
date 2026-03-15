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
# Erdős Problem 136

*Reference:* [erdosproblems.com/136](https://www.erdosproblems.com/136)

Let $f(n)$ be the smallest number of colours required to colour the edges of $K_n$
such that every $K_4$ contains at least 5 colours. Determine the size of $f(n)$.

Asked by Erdős and Gyárfás [Er97b], who proved that $\frac{5}{6}(n-1) < f(n) < n$ and that
$f(9) = 8$. Erdős believed the upper bound is closer to the truth. In fact the
lower bound is: Bennett, Cushman, Dudek, and Pralat [BCDP22] proved that
$f(n) \sim \frac{5}{6}n$. Joos and Mubayi [JoMu22] found a shorter proof.

[Er97b] Erdős, P. and Gyárfás, A., *A variant of the classical Ramsey problem*,
Combinatorica **17** (1997), 459–467.

[BCDP22] Bennett, P., Cushman, R., Dudek, A., and Pralat, P.,
*The Erdős–Gyárfás function f(n,4,5) = 5/6 n + o(n) — so Gyárfás was right*,
arXiv:2207.02920 (2022).

[JoMu22] Joos, F. and Mubayi, D., *Ramsey theory constructions from hypergraph matchings*,
arXiv:2208.12563 (2022).
-/

open Classical Filter

namespace Erdos136

/-- An edge coloring of $K_n$ with colors from $\operatorname{Fin} k$, represented as a function
on unordered pairs of vertices via `Sym2`. -/
def EdgeColoring (n k : ℕ) : Type := Sym2 (Fin n) → Fin k

/-- The set of distinct colors used on edges within vertex subset $S$
under coloring $\chi$, computed over the unordered pairs of distinct vertices in $S$. -/
noncomputable def edgeColors {n k : ℕ} (χ : EdgeColoring n k)
    (S : Finset (Fin n)) : Finset (Fin k) :=
  (S.offDiag.image (fun p => Sym2.mk p)).image χ

/-- A coloring $\chi$ of $K_n$ is $K_4$-five-colored if every 4-element vertex subset
has at least 5 distinct colors on its edges. -/
def IsK4FiveColored {n k : ℕ} (χ : EdgeColoring n k) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (edgeColors χ S).card

/-- $f(n)$: the minimum number of colors $k$ for which there exists a
$K_4$-five-colored edge coloring of $K_n$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ χ : EdgeColoring n k, IsK4FiveColored χ}

/--
Erdős Problem 136 – asymptotic result
(Bennett–Cushman–Dudek–Pralat [BCDP22]; shorter proof by Joos–Mubayi [JoMu22]):
$f(n) \sim \frac{5}{6}n$. That is, for every $\varepsilon > 0$ and all sufficiently large $n$,
$|f(n) / n - 5/6| < \varepsilon$.
-/
@[category research solved, AMS 5]
theorem erdos_136 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |(f n : ℝ) / (n : ℝ) - 5 / 6| < ε := by
  sorry

/--
Erdős–Gyárfás bounds [Er97b]:
For all sufficiently large $n$, $\frac{5}{6}(n-1) < f(n) < n$.
-/
@[category research solved, AMS 5]
theorem erdos_136.variants.bounds :
    ∀ᶠ n : ℕ in atTop,
      (5 : ℝ) / 6 * ((n : ℝ) - 1) < (f n : ℝ) ∧ (f n : ℝ) < (n : ℝ) := by
  sorry

/--
Special value: $f(9) = 8$, proved by Erdős and Gyárfás [Er97b].
-/
@[category research solved, AMS 5]
theorem erdos_136.variants.f9 : f 9 = 8 := by
  sorry

end Erdos136
