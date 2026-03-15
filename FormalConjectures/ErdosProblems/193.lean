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
# Erdős Problem 193

*Reference:* [erdosproblems.com/193](https://www.erdosproblems.com/193)

Let $S \subseteq \mathbb{Z}^3$ be a finite set and let $A = \{a_1, a_2, \ldots\} \subset \mathbb{Z}^3$
be an infinite $S$-walk, so that $a_{i+1} - a_i \in S$ for all $i$. Must $A$ contain three
collinear points?

Originally conjectured by Gerver and Ramsey [GeRa79], who showed that the answer is yes for
$\mathbb{Z}^2$, and for $\mathbb{Z}^3$ that the largest number of collinear points can be bounded.

See also OEIS sequence A231255.

[GeRa79] Gerver, J. and Ramsey, L. T., _On certain sequences of lattice points_.
Pacific J. Math. (1979), 357-363.

[ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory: some problems on additive number theory_. (1979).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos193

/-- Three points in $\mathbb{Z}^3$ are collinear if the difference vectors from the first
to the other two are linearly dependent over $\mathbb{Z}$ (equivalently, over $\mathbb{Q}$). -/
def Collinear3 (p q r : Fin 3 → ℤ) : Prop :=
  ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ k : Fin 3, a * (q k - p k) = b * (r k - p k)

/--
Erdős Problem 193 [ErGr80]:
Let $S \subseteq \mathbb{Z}^3$ be a finite set and let $a : \mathbb{N} \to \mathbb{Z}^3$ be an
injective $S$-walk (i.e. $a(i+1) - a(i) \in S$ for all $i$, visiting infinitely many distinct
points). Then the range of $a$ must contain three collinear points.
-/
@[category research open, AMS 5]
theorem erdos_193 : answer(sorry) ↔
    ∀ (S : Finset (Fin 3 → ℤ)) (a : ℕ → (Fin 3 → ℤ)),
      Function.Injective a →
      (∀ i, a (i + 1) - a i ∈ S) →
      ∃ i j k : ℕ, i < j ∧ j < k ∧ Collinear3 (a i) (a j) (a k) := by
  sorry

/-- Three points in $\mathbb{Z}^2$ are collinear if the difference vectors from the first
to the other two are linearly dependent over $\mathbb{Z}$ (equivalently, over $\mathbb{Q}$). -/
def Collinear3_2D (p q r : Fin 2 → ℤ) : Prop :=
  ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ k : Fin 2, a * (q k - p k) = b * (r k - p k)

/--
Erdős Problem 193, $\mathbb{Z}^2$ case [GeRa79]:
For any finite step set $S \subseteq \mathbb{Z}^2$ and any injective $S$-walk
$a : \mathbb{N} \to \mathbb{Z}^2$, the range of $a$ must contain three collinear points.
This was proved by Gerver and Ramsey, who also conjectured the analogous result for
$\mathbb{Z}^3$ (the main open problem `erdos_193`).
-/
@[category research solved, AMS 5]
theorem erdos_193_Z2 :
    ∀ (S : Finset (Fin 2 → ℤ)) (a : ℕ → (Fin 2 → ℤ)),
      Function.Injective a →
      (∀ i, a (i + 1) - a i ∈ S) →
      ∃ i j k : ℕ, i < j ∧ j < k ∧ Collinear3_2D (a i) (a j) (a k) := by
  sorry

end Erdos193
