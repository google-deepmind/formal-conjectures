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
# Cunningham chains

A Cunningham chain is a sequence of primes satisfying either $p_{i+1}=2p_i+1$
(first kind) or $p_{i+1}=2p_i-1$ (second kind). It is conjectured that there
are infinitely many chains of every positive exact length, of both kinds.

*References:*
- Lenny Jones, [Polynomial Cunningham Chains](https://arxiv.org/abs/1104.1579)
- [OEIS A181697](https://oeis.org/A181697), first-kind chain lengths
- [OEIS A181715](https://oeis.org/A181715), second-kind chain lengths
-/

namespace CunninghamChain

/-- The `n`th term generated from `p` by the first-kind recurrence `q ↦ 2q + 1`. -/
def firstKindTerm (p : ℕ) : ℕ → ℕ
  | 0 => p
  | n + 1 => 2 * firstKindTerm p n + 1

/-- The `n`th term generated from `p` by the second-kind recurrence `q ↦ 2q - 1`. -/
def secondKindTerm (p : ℕ) : ℕ → ℕ
  | 0 => p
  | n + 1 => 2 * secondKindTerm p n - 1

/-- `p` starts a first-kind Cunningham chain of exact positive length `k`. -/
def IsFirstKindChainOfLength (p k : ℕ) : Prop :=
  0 < k ∧ (∀ i < k, (firstKindTerm p i).Prime) ∧ ¬(firstKindTerm p k).Prime

/-- `p` starts a second-kind Cunningham chain of exact positive length `k`. -/
def IsSecondKindChainOfLength (p k : ℕ) : Prop :=
  0 < k ∧ (∀ i < k, (secondKindTerm p i).Prime) ∧ ¬(secondKindTerm p k).Prime

@[category test, AMS 11]
theorem two_starts_firstKind_length_five : IsFirstKindChainOfLength 2 5 := by
  refine ⟨by norm_num, ?_, by norm_num [firstKindTerm]⟩
  intro i hi
  interval_cases i <;> norm_num [firstKindTerm]

@[category test, AMS 11]
theorem seven_starts_secondKind_length_two : IsSecondKindChainOfLength 7 2 := by
  refine ⟨by norm_num, ?_, by norm_num [secondKindTerm]⟩
  intro i hi
  interval_cases i <;> norm_num [secondKindTerm]

/-- There are infinitely many first-kind Cunningham chains of every positive exact length. -/
@[category research open, AMS 11]
theorem infinitely_many_firstKind_chains (k : ℕ) (hk : 0 < k) :
    Set.Infinite {p : ℕ | IsFirstKindChainOfLength p k} := by
  sorry

/-- There are infinitely many second-kind Cunningham chains of every positive exact length. -/
@[category research open, AMS 11]
theorem infinitely_many_secondKind_chains (k : ℕ) (hk : 0 < k) :
    Set.Infinite {p : ℕ | IsSecondKindChainOfLength p k} := by
  sorry

end CunninghamChain
