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

open RatFunc

namespace Erdos351

open Polynomial

/-- The set of rational numbers of the form `P(n) + 1 / n` where `n` is a natural number. -/
def imageSet (P : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ P.eval ↑n + 1 / n)

/-- The predicate that a set is complete, i.e. that it contains all sufficiently large integers. -/
def IsStronglyComplete {α : Type*} [Semiring α] (A : Set α) : Prop :=
  ∀ B : Finset α,
    ∀ᶠ (m : ℕ) in Filter.atTop, ↑m ∈
      { ∑ n ∈ X, n | (X : Finset α) (_ : X.toSet ⊆ A \ B.toSet)}

/-- The predicate that rational polynomial `P` has a complete image. -/
def HasCompleteImage (P : ℚ[X]) : Prop := IsStronglyComplete (imageSet P)

/--
Let $p(x)\in \mathbb{Q}[x]$. Is it true that
\[A=\{ p(n)+1/n : n\in \mathbb{N}\}\]
is strongly complete, in the sense that, for any finite set $B$,
\[\left\{\sum_{n\in X}n : X\subseteq A\backslash B\textrm{ finite }\right\}\]
contains all sufficiently large rational numbers?
-/
@[category research open, AMS 11]
theorem erdos_351 : (∀ P : ℚ[X], HasCompleteImage P) ↔ answer(sorry) := by
  sorry

/--
Let $p(x) = x\in \mathbb{Q}[x]$. It has been shown that
\[A=\{ p(n)+1/n : n\in \mathbb{N}\}\]
is strongly complete, in the sense that, for any finite set $B$,
\[\left\{\sum_{n\in X}n : X\subseteq A\backslash B\textrm{ finite }\right\}\]
contains all sufficiently large rational numbers.
-/
@[category research open, AMS 11]
theorem erdos_351.variants.X : HasCompleteImage X := by
  sorry

end Erdos351
