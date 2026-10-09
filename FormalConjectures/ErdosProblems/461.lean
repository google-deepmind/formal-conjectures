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
# Erdős Problem 461

*References:*
- [erdosproblems.com/461](https://www.erdosproblems.com/461)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980), p. 92.
-/

@[expose] public section

namespace Erdos461

/-- Product of prime factors strictly below `t`, retaining multiplicity.
At zero the empty factor list gives 1; zero never belongs to our intervals. -/
def smoothComponent (t m : ℕ) : ℕ :=
  (m.primeFactorsList.filter (fun p => p < t)).prod

/-- Distinct smooth components in the inclusive interval $[n+1,n+t]$. -/
def smoothValues (n t : ℕ) : Finset ℕ :=
  (Finset.Icc (n + 1) (n + t)).image (smoothComponent t)

/-- The number of distinct smooth components in $[n+1,n+t]$. -/
def count (n t : ℕ) : ℕ := (smoothValues n t).card

/--
Let $s_t(n)$ be the $t$-smooth component of $n$ - that is, the product of all primes $p$
(with multiplicity) dividing $n$ such that $p<t$. Let $f(n,t)$ count the number of distinct
possible values for $s_t(m)$ for $m\in [n+1,n+t]$. Is it true that
$$f(n,t)\gg t$$
(uniformly, for all $t$ and $n$)?

Erdős and Graham report they can show $f(n,t) \gg t/\log t$.
-/
@[category research open, AMS 11]
theorem erdos_461 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, c * (t : ℝ) ≤ (count n t : ℝ) := by sorry

/-- A zero-length interval has no smooth components. -/
@[category API, AMS 11]
theorem count_zero (n : ℕ) : count n 0 = 0 := by
  simp [count, smoothValues]

/-- There are at most $t$ distinct smooth components in an interval of length $t$. -/
@[category API, AMS 11]
theorem count_le (n t : ℕ) : count n t ≤ t := by
  calc
    count n t ≤ (Finset.Icc (n + 1) (n + t)).card := Finset.card_image_le
    _ = t := by simp

/-- A nonempty interval has at least one smooth component. -/
@[category API, AMS 11]
theorem count_pos (n : ℕ) {t : ℕ} (ht : 0 < t) : 0 < count n t := by
  apply Finset.card_pos.mpr
  refine ⟨smoothComponent t (n + 1), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨n + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, rfl⟩

/-- An interval of length one has exactly one smooth component. -/
@[category API, AMS 11]
theorem count_one (n : ℕ) : count n 1 = 1 := by
  simp [count, smoothValues]

end Erdos461
