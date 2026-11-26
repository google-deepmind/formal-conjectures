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
# Mauras's matrix-scaling conjecture for match probabilities

*Reference:* S. Mauras,
[Analysis of Random Models for Stable Matchings](https://www.irif.fr/~mauras/thesis/thesis.pdf),
PhD dissertation, Université de Paris (2021), Conjecture 8.1, p. 105, and Theorem 8.2.

Both sides draw independent complete rankings by weighted sampling without replacement.
The matrices are indexed by man then woman: $P_{mw}$ is the weight man $m$ gives woman $w$,
and $Q_{mw}$ is the weight woman $w$ gives man $m$.
-/

@[expose] public section

open Filter
open scoped Topology NNReal

namespace MaurasMatchProbabilities

/-- A positive diagonal scaling of $P \circ Q$ with every row and column sum equal to one. -/
def IsDoublyStochasticScaling {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X ∈ doublyStochastic ℝ (Fin n) ∧
    ∃ row col : Fin n → ℝ, (∀ m, 0 < row m) ∧ (∀ w, 0 < col w) ∧
      ∀ m w, X m w = row m * (P m w : ℝ) * (Q m w : ℝ) * col w

/-- Probability that a specified man and woman match under men-proposing deferred acceptance. -/
noncomputable def matchProbability {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (m w : Fin n) : ℝ :=
  ((RandomRanking.profile P Q).toMeasure
    {p | (StableMarriage.deferredAcceptance p).held w = some m}).toReal

/-- In a singleton market the unique pair matches with probability one. -/
@[category test, AMS 15 60 91]
theorem matchProbability_one (P Q : Fin 1 → Fin 1 → ℝ≥0) :
    matchProbability P Q 0 0 = 1 := by
  have he : {p : StableMarriage.Profile 1 |
      (StableMarriage.deferredAcceptance p).held 0 = some 0} = Set.univ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hp : p = default := by
      cases p
      congr <;> exact Subsingleton.elim _ _
    subst p
    decide
  simp [matchProbability, he]

/-- Uniform weights admit the uniform doubly stochastic scaling at every positive size. -/
@[category test, AMS 15 60 91]
theorem uniform_scaling (n : ℕ) :
    IsDoublyStochasticScaling (fun _ _ ↦ 1) (fun _ _ ↦ 1)
      (Matrix.of fun _ _ : Fin (n + 1) ↦ 1 / (n + 1 : ℝ)) := by
  have h : (n + 1 : ℝ) ≠ 0 := by positivity
  refine ⟨?_, fun _ ↦ 1 / (n + 1 : ℝ), fun _ ↦ 1, fun _ ↦ by positivity,
    fun _ ↦ by norm_num, fun _ _ ↦ by simp⟩
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨fun _ _ ↦ by dsimp; positivity, fun _ ↦ by simp [h], fun _ ↦ by simp [h]⟩

/--
Conjecture 8.1: for weights in a fixed interval $[1,C]$, the probability of a pair matching is
$X_{mw}+o(1/n)$, where $X$ is the doubly stochastic scaling of $P \circ Q$.
The quantified pair may vary with market size. We use size $n+1$ so that pairs always exist.
-/
@[category research open, AMS 15 60 91]
theorem pair_match_probability
    (C : ℝ≥0) (hC : 1 ≤ C)
    (P Q : (n : ℕ) → Fin (n + 1) → Fin (n + 1) → ℝ≥0)
    (hP : ∀ n m w, 1 ≤ P n m w ∧ P n m w ≤ C)
    (hQ : ∀ n m w, 1 ≤ Q n m w ∧ Q n m w ≤ C)
    (X : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hX : ∀ n, IsDoublyStochasticScaling (P n) (Q n) (X n))
    (m w : (n : ℕ) → Fin (n + 1)) :
    Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) *
      (matchProbability (P n) (Q n) (m n) (w n) - X n (m n) (w n)))
      atTop (𝓝 0) := by
  sorry

end MaurasMatchProbabilities
