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
# Cunningham chains — Jones's conjecture

A Cunningham chain is a sequence of primes satisfying either $p_{i+1}=2p_i+1$
(first kind) or $p_{i+1}=2p_i-1$ (second kind). It is conjectured that there
are infinitely many chains of every positive exact length, of both kinds.

A chain has **exact length k** when its first $k$ terms are prime and the
$(k+1)$-th generated term is composite.

Lenny Jones conjectures that for every positive integer $k$, infinitely many
primes start a chain of exact length $k$, for each of the two kinds.

*References:*
- Lenny Jones, [Polynomial Cunningham Chains](https://arxiv.org/abs/1104.1579)
- [OEIS A181697](https://oeis.org/A181697), first-kind chain lengths
- [OEIS A181715](https://oeis.org/A181715), second-kind chain lengths
-/

namespace CunninghamChain

/-- The `n`th term generated from `p` by the first-kind recurrence `q ↦ 2q + 1`. -/
def firstKindTerm (p : ℕ) : ℕ → ℕ
  | 0     => p
  | n + 1 => 2 * firstKindTerm p n + 1

/-- The `n`th term generated from `p` by the second-kind recurrence `q ↦ 2q - 1`. -/
def secondKindTerm (p : ℕ) : ℕ → ℕ
  | 0     => p
  | n + 1 => 2 * secondKindTerm p n - 1

/-- `p` starts a first-kind Cunningham chain of exact positive length `k`. -/
def IsFirstKindChainOfLength (p k : ℕ) : Prop :=
  0 < k ∧ (∀ i < k, (firstKindTerm p i).Prime) ∧ ¬(firstKindTerm p k).Prime

/-- `p` starts a second-kind Cunningham chain of exact positive length `k`. -/
def IsSecondKindChainOfLength (p k : ℕ) : Prop :=
  0 < k ∧ (∀ i < k, (secondKindTerm p i).Prime) ∧ ¬(secondKindTerm p k).Prime

-- Sanity-check: 2 starts a first-kind chain of length 5
-- (2, 5, 11, 23, 47 are prime; 2·47+1 = 95 = 5·19 is composite)
@[category test, AMS 11]
theorem two_starts_firstKind_length_five : IsFirstKindChainOfLength 2 5 := by
  refine ⟨by norm_num, ?_, by norm_num [firstKindTerm]⟩
  intro i hi
  interval_cases i <;> norm_num [firstKindTerm]

-- Sanity-check: 7 starts a second-kind chain of length 2
-- (7, 13 are prime; 2·13-1 = 25 = 5² is composite)
@[category test, AMS 11]
theorem seven_starts_secondKind_length_two : IsSecondKindChainOfLength 7 2 := by
  refine ⟨by norm_num, ?_, by norm_num [secondKindTerm]⟩
  intro i hi
  interval_cases i <;> norm_num [secondKindTerm]

/--
Jones's conjecture (first kind): for every positive integer $k$, there are
infinitely many primes $p$ that start a first-kind Cunningham chain of
exactly length $k$.
-/
@[category research open, AMS 11]
theorem infinitely_many_firstKind_chains (k : ℕ) (hk : 0 < k) :
    Set.Infinite {p : ℕ | IsFirstKindChainOfLength p k} := by
  sorry

/--
Jones's conjecture (second kind): for every positive integer $k$, there are
infinitely many primes $p$ that start a second-kind Cunningham chain of
exactly length $k$.
-/
@[category research open, AMS 11]
theorem infinitely_many_secondKind_chains (k : ℕ) (hk : 0 < k) :
    Set.Infinite {p : ℕ | IsSecondKindChainOfLength p k} := by
  sorry

end CunninghamChain
