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
# Erdős Problem 1112

*References:*
- [erdosproblems.com/1112](https://www.erdosproblems.com/1112)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory*. Monogr. Enseign. Math. **28** (1980).

The definitions and the statement below mirror the frozen statement file of the Lean
development linked from `erdos_1112`, so that the two encodings cannot drift apart.
-/

namespace Erdos1112

/-- `B` (as a strictly increasing enumeration of an infinite set of positive
integers) is *lacunary with ratio `r`*: `b₁ ≥ 1`, `b₁ < b₂ < ⋯`, and
`b_{i+1} ≥ r · b_i` for all `i`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- `A` (as a strictly increasing enumeration of an infinite set of positive
integers) has all consecutive gaps in `[d₁, d₂]`: `d₁ ≤ a_{i+1} − a_i ≤ d₂` for
all `i`.

Phrased additively to dodge `ℕ`-truncated subtraction: an isolated upper bound
`a (i+1) − a i ≤ d₂` would underflow to `0 ≤ d₂` and silently admit negative gaps. -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- For `1 ≤ d₁`, the gap condition forces `A` strictly increasing: this makes
explicit that `A` enumerates an infinite set, as the problem intends. -/
@[category API, AMS 5 11]
lemma HasGapsIn.strictMono {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) : StrictMono a :=
  strictMono_nat_of_lt_succ fun i =>
    lt_of_lt_of_le (Nat.lt_add_of_pos_right hd₁) (h.2 i).1

/-- The `k`-fold sumset `kA` of the set enumerated by `a`: all sums
`a_{i₁} + ⋯ + a_{i_k}`, indices arbitrary and repetitions allowed — the intended
`kA`, not the smaller distinct-summand set. -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- The property asked for by the problem, for given `k`, `d₁`, `d₂` and a
candidate `r`: *every* lacunary sequence `B` with ratio `r` admits a set `A`
with gaps in `[d₁, d₂]` such that `(kA) ∩ B = ∅`. -/
def RatioWorks (k d₁ d₂ r : ℕ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWith r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

/-- `RatioWorks` is monotone in the ratio: a larger `r` only shrinks the class of
admissible `B`. This machine-checks the reduction from the problem's "an integer
`r`" to `r : ℕ` in `Question`: any integer witness may be replaced by any larger
natural one. -/
@[category API, AMS 5 11]
lemma RatioWorks.mono {k d₁ d₂ r r' : ℕ} (hrr' : r ≤ r')
    (h : RatioWorks k d₁ d₂ r) : RatioWorks k d₁ d₂ r' := by
  intro b hb
  exact h b ⟨hb.1, hb.2.1, fun i => (Nat.mul_le_mul hrr' le_rfl).trans (hb.2.2 i)⟩

/-- **Erdős Problem 1112**, verbatim question:

"Let `1 ≤ d₁ < d₂` and `k ≥ 3`. Does there exist an integer `r` such that if
`B = {b₁ < b₂ < ⋯}` is a lacunary sequence with `b_{i+1} ≥ r·b_i` then there
exists `A = {a₁ < a₂ < ⋯}` with `d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` and
`(kA) ∩ B = ∅`?"

Note the quantifier order: `∃ r, ∀ B, ∃ A …` places `A` after `B`. -/
def Question (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, RatioWorks k d₁ d₂ r

/--
Let $k \geq 3$ and $1 \leq d_1 < d_2$. Does there exist an integer $r$ such that every
lacunary sequence $B = \{b_1 < b_2 < \cdots\}$ with $b_{i+1} \geq r b_i$ admits a
sequence $A = \{a_1 < a_2 < \cdots\}$ with $d_1 \leq a_{i+1} - a_i \leq d_2$ for all $i$
and $(kA) \cap B = \emptyset$?

This has been **solved**: such an $r$ exists if and only if $d_2 \geq k+1$.
-/
@[category research solved, formal_proof using lean4 at
  "https://github.com/beetree/math_erdos_1112", AMS 5 11]
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    Question k d₁ d₂ ↔ answer(k + 1 ≤ d₂) := by
  sorry

end Erdos1112
