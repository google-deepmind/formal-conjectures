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

module

public import FormalConjecturesUtil

/-!
# Erdős Problem 472

*References:*
- [erdosproblems.com/472](https://www.erdosproblems.com/472)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*, Monographies de L'Enseignement Mathématique (1980), p.94.
-/

@[expose] public section

namespace Erdos472

/-- Allowed partner indices at stage `k`. Inclusive history permits the current term. -/
def Allowed (includeLast : Bool) (i k : ℕ) : Prop :=
  if includeLast then i ≤ k else i < k

/-- A prime of the form $q_k + q_i - 1$ for an allowed historical index $i$. -/
def Candidate (includeLast : Bool) (q : ℕ → ℕ) (k p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ i, Allowed includeLast i k ∧ p = q k + q i - 1

/-- The next term is the least prime candidate. -/
def GreedyStep (includeLast : Bool) (q : ℕ → ℕ) (k : ℕ) : Prop :=
  Candidate includeLast q k (q (k + 1)) ∧
    ∀ p, Candidate includeLast q k p → q (k + 1) ≤ p

/-- An infinite increasing prime sequence extending a nonempty seed of length $m$.
Indices start at zero, so the first extension is at stage $m-1$. -/
def InfiniteOrbit (includeLast : Bool) (m : ℕ) (q : ℕ → ℕ) : Prop :=
  0 < m ∧ StrictMono q ∧ (∀ k, Nat.Prime (q k)) ∧
    ∀ k, m ≤ k + 1 → GreedyStep includeLast q k

/--
Given some initial finite sequence of primes $q_1<\cdots<q_m$ extend it so that $q_{n+1}$ is the
smallest prime of the form $q_n+q_i-1$ for $n\geq m$. Is there an initial starting sequence so
that the resulting sequence is infinite?

A problem of Ulam [ErGr80, p.94]. The book restricts the partner to $1\leq i<n$.
-/
@[category research open, AMS 11]
theorem erdos_472 : answer(sorry) ↔
    ∃ m, ∃ q : ℕ → ℕ, InfiniteOrbit false m q := by
  sorry

/-- Does the process continue forever if the current term is also an allowed partner,
so that $1\leq i\leq n$? This is an alternative interpretation of the unspecified index
range on the website. -/
@[category research open, AMS 11]
theorem erdos_472.variants.inclusive_history : answer(sorry) ↔
    ∃ m, ∃ q : ℕ → ℕ, InfiniteOrbit true m q := by
  sorry

/-- Does the strict-history process starting from $3,5$ continue forever [ErGr80, p.94]? -/
@[category research open, AMS 11]
theorem erdos_472.variants.seed_three_five : answer(sorry) ↔
    ∃ q : ℕ → ℕ, InfiniteOrbit false 2 q ∧ q 0 = 3 ∧ q 1 = 5 := by
  sorry

/-- A singleton seed cannot extend under the strict-history rule. -/
@[category textbook, AMS 11]
theorem no_strict_singleton_orbit (q : ℕ → ℕ) : ¬ InfiniteOrbit false 1 q := by
  intro h
  obtain ⟨_, i, hi, _⟩ := (h.2.2.2 0 (by omega)).1
  simp [Allowed] at hi

/-- The seed $3,7$ stops under strict history but has the inclusive candidate $13$. -/
@[category test, AMS 11]
theorem history_rules_differ :
    ∃ q : ℕ → ℕ, q 0 = 3 ∧ q 1 = 7 ∧
      (¬ ∃ p, Candidate false q 1 p) ∧ Candidate true q 1 13 := by
  refine ⟨fun n ↦ if n = 0 then 3 else 7, by simp, by simp, ?_, ?_⟩
  · rintro ⟨p, hp, i, hi, he⟩
    have hi0 : i = 0 := by simpa [Allowed] using hi
    subst i
    norm_num at he
    subst p
    norm_num at hp
  · refine ⟨by norm_num, 1, ?_, ?_⟩ <;> norm_num [Allowed]

end Erdos472
