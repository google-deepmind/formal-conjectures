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
# Erdős Problem 434

*Reference:* [erdosproblems.com/434](https://www.erdosproblems.com/434)
-/
/--
A natural $n$ is representable as a set $A$ if it can be
written as the sum of finitely many elements of $A$
(with repetition allowed).
-/
abbrev Nat.IsRepresentableAs (n : ℕ) (A : Set ℕ) :=
    ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = n

/--
The number of naturals that cannot be written as the sum of
finitely many elements of the set $A$, with repetition allowed.
-/
noncomputable abbrev Nat.NcardUnrepresentable (A : Set ℕ) :=
    { n : ℕ | ¬n.IsRepresentableAs A }.ncard

/--
Let $k\leq n$. What choice of $A\subseteq\{1, \dots, n\}$ of size $|A| = k$
maximises the number of integers not representable as the sum of finitely
many elements from $A$ (with repetitions allowed)?
Is it $\{n, n - 1, ..., n - k + 1\}$?
-/
@[category research open, AMS 11]
theorem erdos_434.parts.i (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (h : k ≤ n) :
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Set ℕ) (_ : S ⊆ Set.Icc 1 n) (_ : S.ncard = k) }
      (Nat.NcardUnrepresentable <| answer(sorry)) :=
  sorry

/--
Let $k\leq n$. Out of all $A\subseteq\{1, \dots, n\}$ of size $|A| = k$,
does $A = \{n, n - 1, ..., n - k + 1\}$ maximise the number of integers
not representable as the sum of finitely many elements from $A$ (with repetitions allowed)?
-/
@[category research open, AMS 11]
theorem erdos_434.parts.ii (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (h : k ≤ n) :
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Set ℕ) (_ : S ⊆ Set.Icc 1 n) (_ : S.ncard = k) }
      (Nat.NcardUnrepresentable <| Set.Icc (n - k + 1 : ℕ) n) :=
  sorry
