/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 351

*Reference:* [erdosproblems.com/351](https://www.erdosproblems.com/351)
-/

open Polynomial

namespace Erdos351

/-- The set of rational numbers of the form `P(n) + 1 / n` where `n` is a natural number
and `P` is a polynomial with rational coefficients.

Note: We include `P 0` in there (since `1 / 0 = 0`), but this doesn't change the validity of the
conjecture -/
def imageSet {α : Type*} [Semifield α] (P : α[X]) : Set α :=
  Set.range (fun (n : ℕ) ↦ P.eval ↑n + 1 / n)

/-- The predicate that a set `A` is strongly complete, i.e. that for every finite set `B`, every sufficiently
large integer is a sum of elements of the set `A \ B`. -/
def IsStronglyComplete {α : Type*} [Semiring α] (A : Set α) : Prop :=
  ∀ B : Finset α,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ↑m ∈ { ∑ n ∈ X, n | (X : Finset α) (_ : ↑X ⊆ A \ B) }

/-- The predicate that the rational polynomial `P` has a complete image. -/
def HasCompleteImage (P : ℚ[X]) : Prop := IsStronglyComplete (imageSet P)

/--
Let $p(x) \in \mathbb{Q}[x]$ be a non-constant rational polynomial with positive leading
coefficient. Is it true that \[A=\{ p(n)+1/n : n \in \mathbb{N}\}\] is strongly complete,
in the sense that, for any finite set $B$,
\[\left\{\sum_{a \in X} a : X \subseteq A \setminus B, X \textrm{ is finite}\right\}\]
contains all sufficiently large integers? -/
@[category research open, AMS 11]
theorem erdos_351 :
    answer(sorry) ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff → HasCompleteImage P := by
  sorry

/--
Let $p(x) = x \in \mathbb{Q}[x]$. It has been shown that
\[A=\{ p(n)+1/n : n \in \mathbb{N}\}\]
is strongly complete, in the sense that, for any finite set $B$,
\[\left\{\sum_{a \in X} a : X \subseteq A \setminus B, X \textrm{ is finite}\right\}\]
contains all sufficiently large integers.
-/
@[category research solved, AMS 11]
protected theorem erdos_351.variants.X : HasCompleteImage X := by
  sorry

/-- Let $p(x) = x ^ 2 \in \mathbb{Q}[x]$. It has been shown that
\[A=\{ p(n)+1/n : n \in \mathbb{N}\}\]
is strongly complete, in the sense that, for any finite set $B$,
\[\left\{\sum_{a \in X} a : X \subseteq A \setminus B, X \textrm{ is finite}\right\}\]
contains all sufficiently large integers. -/
@[category research solved, AMS 11]
theorem erdos_351.variants.X_sq : HasCompleteImage (X ^ 2) := by
  sorry

end Erdos351
