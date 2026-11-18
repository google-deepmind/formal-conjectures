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
# Barker sequences

A Barker sequence is a finite sequence of $\pm 1$ values whose nontrivial aperiodic
autocorrelations all have magnitude at most one. The Barker conjecture says that no such sequence
has length greater than $13$.

Turyn and Storer [TS61] showed that an odd-length Barker sequence has length at most $13$. Willms
found a gap in their proof, and Schmidt and Willms [SW15] gave a corrected and simpler proof. A Barker sequence of even length $n > 4$ would give a
circulant Hadamard matrix of order $n$. OpenAI [OAI26] proved the circulant Hadamard conjecture,
and with it that every even-length Barker sequence has length $2$ or $4$.

*References:*
* J. Willms, [A note on Barker sequences of even length](https://arxiv.org/abs/2104.00502)
* [Barker code](https://en.wikipedia.org/wiki/Barker_code)
* [OEIS A091704](https://oeis.org/A091704)
* [TS61] R. Turyn and J. Storer, *On binary sequences*, Proc. Amer. Math. Soc. 12 (1961), 394–399.
* [SW15] K.-U. Schmidt and J. Willms, *Barker sequences of odd length*,
  [arXiv:1501.06035](https://arxiv.org/abs/1501.06035)
* [OAI26] OpenAI, *The circulant Hadamard conjecture*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-circulant-Hadamard-conjecture-September-23-2026/paper.pdf
-/

@[expose] public section

namespace Arxiv.«2104.00502»

/-- The aperiodic autocorrelation $C_k(a)=\sum_i a_i a_{i+k}$. -/
def aperiodicAutocorrelation (a : List ℤ) (k : ℕ) : ℤ :=
  (List.zipWith (· * ·) a (a.drop k)).sum

/--
A Barker sequence has $\pm 1$ entries and nontrivial autocorrelations of magnitude at most one.
-/
def IsBarkerSequence (a : List ℤ) : Prop :=
  (∀ x ∈ a, x = 1 ∨ x = -1) ∧
    ∀ k : ℕ, 0 < k → k < a.length → |aperiodicAutocorrelation a k| ≤ 1

/--
Every Barker sequence has length at most $13$. This follows from the odd case [TS61, SW15] and the
even case [OAI26]; see `barker_conjecture_of_odd_of_even`.
-/
@[category research solved, AMS 5 11 94]
theorem barker_conjecture (a : List ℤ) (ha : IsBarkerSequence a) : a.length ≤ 13 := by
  sorry

/-- Every Barker sequence of odd length has length at most $13$ [TS61, SW15]. -/
@[category research solved, AMS 5 11 94]
theorem barker_conjecture.variants.odd (a : List ℤ) (hodd : Odd a.length)
    (ha : IsBarkerSequence a) : a.length ≤ 13 := by
  sorry

/-- Every Barker sequence of positive even length has length $2$ or $4$ [OAI26]. -/
@[category research solved, AMS 5 11 94]
theorem barker_conjecture.variants.even (a : List ℤ) (hpos : 0 < a.length)
    (heven : Even a.length) (ha : IsBarkerSequence a) : a.length = 2 ∨ a.length = 4 := by
  sorry

/-- The odd and even cases give the Barker conjecture. -/
@[category test, AMS 5 11 94]
theorem barker_conjecture_of_odd_of_even (hodd : type_of% barker_conjecture.variants.odd)
    (heven : type_of% barker_conjecture.variants.even) : type_of% barker_conjecture := by
  intro a ha
  rcases Nat.even_or_odd a.length with h | h
  · rcases Nat.eq_zero_or_pos a.length with h0 | h0
    · omega
    · rcases heven a h0 h ha with h2 | h4 <;> omega
  · exact hodd a h ha

/--
The known sequence $(1,1,1,1,1,-1,-1,1,1,-1,1,-1,1)$ of length $13$ is a Barker sequence.
-/
@[category test, AMS 5 11 94]
theorem isBarkerSequence_length_thirteen :
    IsBarkerSequence [1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1] := by
  constructor
  · simp
  · intro k hkpos hklen
    norm_num at hklen
    interval_cases k <;>
      norm_num [aperiodicAutocorrelation] at hkpos ⊢

/-- The sequence $(1,1,1,-1)$ is a Barker sequence. -/
@[category test, AMS 5 11 94]
theorem isBarkerSequence_length_four : IsBarkerSequence [1, 1, 1, -1] := by
  constructor
  · simp
  · intro k hkpos hklen
    norm_num at hklen
    interval_cases k <;>
      norm_num [aperiodicAutocorrelation] at hkpos ⊢

/-- The constant sequence $(1,1,1,1)$ is not a Barker sequence. -/
@[category test, AMS 5 11 94]
theorem not_isBarkerSequence_constant_four : ¬ IsBarkerSequence [1, 1, 1, 1] := by
  intro ha
  have h := ha.2 1 (by norm_num) (by norm_num)
  norm_num [aperiodicAutocorrelation] at h

end Arxiv.«2104.00502»
