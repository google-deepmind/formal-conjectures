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
# Minimum modulus for the unique multiset-sum problem

*References:*
- [arxiv/2607.08366](https://arxiv.org/abs/2607.08366)
  **Minimum modulus for the unique multiset-sum problem**
  by *José A. R. Fonollosa*
- [jarfo/min-modulus](https://github.com/jarfo/min-modulus), the author's Lean development of
  the paper's Main Theorem. Section 7 of the paper describes it.

The paper's Main Theorem fixes the super-increasing set $\{2^k - 1\}$ and pins the least modulus
at which *it* is valid. Conjecture 1 says no other set of $n$ residues does better, and is open.
-/

open Finset

namespace Arxiv.«2607.08366»

variable {N : ℕ}

/-- `A` is *valid mod* `N` when the all-ones multiset is the only multiset of size `#A` drawn
from `A` whose sum matches `∑ a ∈ A, a`.

`m a` is how many copies of `a` the multiset uses, so the all-ones multiset is `m = 1`. -/
def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = #A → ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

/-- The least modulus admitting a valid set of `n` residues, conjecturally
$2^n - 2^{\lfloor\log_2 n\rfloor}$. -/
def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

/--
**Conjecture 1 (Fonollosa, 2026).** For every $n \geq 2$ and every
$N < 2^n - 2^{\lfloor \log_2 n\rfloor}$, no set of $n$ residues mod $N$ is valid.

Equivalently the super-increasing set $\{2^k - 1 : 0 \leq k \leq n-1\}$ attains the least
valid modulus, which is `minModulus n`.

`0 < N` excludes `N = 0`, where `ZMod 0` is `ℤ` rather than a finite modulus and `{1, 2}` is
valid, which would make the statement false for a reason unrelated to the question.
-/
@[category research open, AMS 11]
theorem min_modulus :
    answer(sorry) ↔ ∀ n N : ℕ, 2 ≤ n → 0 < N → N < minModulus n →
      ∀ A : Finset (ZMod N), #A = n → ¬ IsValidMod A := by
  sorry

/--
**Theorem A (Fonollosa, 2026).** `minModulus n` admits a valid set of `n` residues, the
super-increasing set $\{2^k - 1 : 0 \leq k \leq n - 1\}$. This bounds the least valid modulus
from above; that no smaller modulus works is the open half, stated in `min_modulus`.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/jarfo/min-modulus/blob/e7c78dd63955092b5f8d8a5fa826476337c0f4be/MinModulus/UniqueSums.lean#L837-L838"]
theorem exists_isValidMod_minModulus (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A := by
  sorry

/-- The all-ones multiset always has the right size and the right sum, so `IsValidMod` is a
uniqueness statement rather than an existence one. -/
@[category API, AMS 11]
theorem one_sum_eq (A : Finset (ZMod N)) :
    ∑ _a ∈ A, (1 : ℕ) = #A ∧ ∑ a ∈ A, ((1 : ℕ) : ZMod N) * a = ∑ a ∈ A, a :=
  ⟨by simp, by simp⟩

/-- A set with fewer than two elements is valid for a silly reason, so the conjecture asks
about `2 ≤ n`: with `#A ≤ 1` the only multiset of size `#A` drawn from `A` is the all-ones one. -/
@[category API, AMS 11]
theorem isValidMod_of_subsingleton {A : Finset (ZMod N)} (hA : #A ≤ 1) : IsValidMod A := by
  intro m hsize _ a ha
  rcases Finset.card_le_one.mp hA with h
  have : A = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun b hb => h b hb a ha⟩
  subst this
  simpa using hsize

end Arxiv.«2607.08366»
