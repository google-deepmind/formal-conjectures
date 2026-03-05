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
# Erdős Problem 129

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)

Let $R(n; k, r)$ be the smallest $N$ such that if the edges of $K_N$ are $r$-coloured
then there is a set of $n$ vertices which does not contain a copy of $K_k$ in at
least one of the $r$ colours. Erdős and Gyárfás conjectured that there exists a
constant $C = C(r) > 1$ such that $R(n; 3, r) < C^{\sqrt{n}}$.

As pointed out by Antonio Girao, the problem as stated is easily
disproved. A probabilistic argument shows $R(n; 3, 2) \geq C^n$ for some $C > 1$,
contradicting the claimed bound. The correct formulation is unclear.

[Er97b] Erdős, P. and Gyárfás, A., *A variant of the classical Ramsey problem*,
Combinatorica **17** (1997), 459–467.
-/

namespace Erdos129

/-- An $r$-edge-coloring of the complete graph $K_N$: a function that assigns a
color in $\operatorname{Fin} r$ to each ordered pair of distinct vertices. -/
def EdgeColoring (N r : ℕ) : Type := Fin N → Fin N → Fin r

/-- A vertex set $S$ is monochromatic-$K_k$-free in color $c$ under coloring $\chi$ if
there is no $k$-element subset of $S$ in which every pair of distinct vertices
receives color $c$. -/
def IsMonoKkFree {N r : ℕ} (χ : EdgeColoring N r) (c : Fin r)
    (k : ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ χ x y ≠ c

/-- The generalized Ramsey number $R(n; k, r)$: the smallest $N$ such that for
every $r$-coloring of the edges of $K_N$, there exists a set of $n$ vertices and
a color $c$ such that the set is $K_k$-free in color $c$. -/
noncomputable def multicolorRamseyNum (n k r : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (χ : EdgeColoring N r),
    ∃ (S : Finset (Fin N)) (c : Fin r),
      S.card = n ∧ IsMonoKkFree χ c k S}

/--
Erdős–Gyárfás Conjecture (Problem 129) [Er97b]:
For every $r \geq 1$, does there exist a constant $C = C(r) > 1$ such that
$R(n; 3, r) < C^{\sqrt{n}}$ for all positive integers $n$?

As observed by Antonio Girao, the problem as stated is easily disproved:
a probabilistic coloring of $K_N$ (each edge independently uniformly at random
in $r$ colors) shows $R(n; 3, 2) \geq C^n$, contradicting the conjecture.
-/
@[category research solved, AMS 5]
theorem erdos_129 : answer(False) ↔
    ∀ r : ℕ, 1 ≤ r →
      ∃ C : ℝ, 1 < C ∧
        ∀ n : ℕ, (multicolorRamseyNum n 3 r : ℝ) < C ^ Real.sqrt (n : ℝ) := by
  sorry

end Erdos129
