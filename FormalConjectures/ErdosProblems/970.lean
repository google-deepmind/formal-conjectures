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
# Erdős Problem 970

*References:*
- [erdosproblems.com/970](https://www.erdosproblems.com/970)
- [FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence,
  *Long gaps between primes*. J. Amer. Math. Soc. (2018), 65-105.
- [Iw78] Iwaniec, Henryk, *On the problem of {J}acobsthal*. Demonstratio Math. (1978), 225--231.
- [OAI26a] OpenAI, *A quadratic bound for Jacobsthal's function*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf
-/

@[expose] public section

namespace Erdos970

/--
`IsJacobsthalBound k m` says that every interval of `m` consecutive integers contains an
integer coprime to every positive natural number having at most `k` distinct prime factors.
-/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/--
Jacobsthal's function, uniformly parametrized by the maximum number of distinct prime factors.
-/
noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

set_option linter.style.formal_proof_palomar false in
/--
Let $h(k)$ be Jacobsthal's function, defined to as the minimal $m$ such that, if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive integers there exists an integer coprime to $n$. Determine the order of magnitude of $h(k)$. In particular, is it true that $$h(k) \ll k^2?$$

The bound $h(k) \ll k^2$ was proved by an internal OpenAI model in September 2026 [OAI26a]; see
the linked Lean proof. The order of magnitude of $h(k)$ remains open. The linked statement is
`erdos_970.variants.exists_bound`; see `erdos_970_of_exists_bound`.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Conclusions/QuadraticBound.lean#L13"]
theorem erdos_970 :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The stronger bound $$h(k) \ll \frac{k^2}{(\log\log 3k)^2}$$ proved in [OAI26a]. The linked
statement is `erdos_970.variants.iterated_log_exists_bound`; see
`erdos_970_iterated_log_of_exists_bound`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Conclusions/IteratedLogBound.lean#L59"]
theorem erdos_970.variants.iterated_log :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 / (Real.log (Real.log (3 * k))) ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The statement of the linked Lean proof of `erdos_970`, with its definitions unfolded: the
bound is given by some `m` with `IsJacobsthalBound k m`, not by `jacobsthalFunction k`. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Conclusions/QuadraticBound.lean#L13"]
theorem erdos_970.variants.exists_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The statement of the linked Lean proof of `erdos_970.variants.iterated_log`, with its
definitions unfolded. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Conclusions/IteratedLogBound.lean#L59"]
theorem erdos_970.variants.iterated_log_exists_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, IsJacobsthalBound k m ∧
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 := by
  sorry

/-- `jacobsthalFunction k` is at most any `m` with `IsJacobsthalBound k m`. -/
@[category test, AMS 11]
theorem erdos_970_of_exists_bound (h : type_of% erdos_970.variants.exists_bound) :
    type_of% erdos_970 := by
  obtain ⟨C, hC, hk⟩ := h
  refine ⟨C, hC, fun k hk0 => ?_⟩
  obtain ⟨m, hm, hmC⟩ := hk k hk0
  exact le_trans (Nat.cast_le.mpr (Nat.sInf_le hm)) hmC

/-- `jacobsthalFunction k` is at most any `m` with `IsJacobsthalBound k m`. -/
@[category test, AMS 11]
theorem erdos_970_iterated_log_of_exists_bound
    (h : type_of% erdos_970.variants.iterated_log_exists_bound) :
    type_of% erdos_970.variants.iterated_log := by
  obtain ⟨C, hC, hk⟩ := h
  refine ⟨C, hC, fun k hk0 => ?_⟩
  obtain ⟨m, hm, hmC⟩ := hk k hk0
  exact le_trans (Nat.cast_le.mpr (Nat.sInf_le hm)) hmC

end Erdos970
