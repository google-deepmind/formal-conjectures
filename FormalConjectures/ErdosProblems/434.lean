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

import FormalConjecturesUtil

/-!
# Erdős Problem 434

*References:*
- [erdosproblems.com/434](https://www.erdosproblems.com/434)
- [Ki02] Kiss, G., On the extremal Frobenius problem in a new aspect. Ann. Univ. Sci.
  Budapest. Eötvös Sect. Math. (2002), 139–142.
-/

namespace Erdos434

open Erdos434 Finset

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
Let $k \le n$. What choice of $A\subseteq\{1, \dots, n\}$ (with $\text{gcd}(A) = 1$) of size $|A| = k$
maximises the number of integers not representable as the sum of finitely
many elements from $A$ (with repetitions allowed)?
Is it $\{n, n - 1, \dots, n - k + 1\}$?

The maximal choice is indeed $\{n, \dots, n - k + 1\}$, as proved by Kiss [Ki02].

The Lean theorem assumes $2 \le k$. When $k = 1 < n$, the proposed singleton $\{n\}$ does not
have gcd $1$; the gcd condition instead forces the unique admissible choice $A = \{1\}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://www.erdosproblems.com/forum/thread/434#post-4437"]
theorem erdos_434.parts.i (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| answer(Set.Icc (n - k + 1 : ℕ) n)) := by
  sorry

/--
For $2 \le k \le n$, the interval $A = \{n, n - 1, \dots, n - k + 1\}$ maximises the number
of integers not representable as the sum of finitely many elements from $A$ (with repetitions
allowed), as proved by Kiss [Ki02].
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://www.erdosproblems.com/forum/thread/434#post-4437"]
theorem erdos_434.parts.ii : answer(True) ↔ ∀ᵉ (n ≥ 1) (k ≥ 2), k ≤ n →
    IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1)}
      (Nat.NcardUnrepresentable <| Set.Icc (n - k + 1 : ℕ) n) := by
  sorry

end Erdos434
