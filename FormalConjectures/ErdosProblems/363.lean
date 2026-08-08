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
# Erdős Problem 363

*References:*
- [erdosproblems.com/363](https://www.erdosproblems.com/363)
- [BaBe07] Bauer, Mark and Bennett, Michael A., *On a question of Erd\H{o}s
  and Graham*. Enseign. Math. (2) (2007), 259--264.
- [BeVL12] Bennett, Michael A. and Van Luijk, Ronald, *Squares from blocks of
  consecutive integers: a problem of Erd\H{o}s and Graham*. Indag. Math. (N.S.)
  (2012), 123--127.
- [Ul05] Ulas, Maciej, *On products of disjoint blocks of consecutive integers*.
  Enseign. Math. (2) (2005), 331--334.
-/

namespace Erdos363

open Finset

/-- A finite set of naturals is an interval of naturals. -/
def IsInterval (I : Finset ℕ) : Prop :=
  ∃ a b : ℕ, I = Icc a b

/-- A collection of intervals as in Erdős Problem 363. -/
def IsValidCollection (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, IsInterval I) ∧
  (∀ I ∈ S, 4 ≤ I.card) ∧
  S.Pairwise Disjoint ∧
  IsSquare ((S.map (fun I => ∏ m ∈ I, m)).prod)

/--
Is it true that there are only finitely many collections of disjoint intervals $I_1,\ldots,I_n$ of size $\lvert I_i\rvert \geq 4$ for $1\leq i\leq n$ such that$$\prod_{1\leq i\leq n}\prod_{m\in I_i}m$$is a square?

This is false: Ulas [Ul05] constructed infinitely many such collections.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos363.lean"]
theorem erdos_363 : answer(False) ↔ {S : List (Finset ℕ) | IsValidCollection S}.Finite := by
  sorry

end Erdos363
