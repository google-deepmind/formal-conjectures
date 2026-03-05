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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1112

*Reference:* [erdosproblems.com/1112](https://www.erdosproblems.com/1112)

Define $r_k(d_1, d_2)$ to be the smallest integer $r$ such that for any lacunary sequence $B$
with ratio $\geq r$, there exists a sequence $A$ with consecutive gaps in $[d_1, d_2]$ whose
$k$-fold sumset avoids $B$. The problem asks whether $r_k(d_1, d_2)$ exists for $k \geq 3$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos1112

/-- The $k$-fold sumset of a set $S$ of natural numbers: all sums $s_1 + \cdots + s_k$
with each $s_i \in S$. Defined recursively: $0S = \{0\}$,
$(k+1)S = \{a + b \mid a \in S,\, b \in kS\}$. -/
def kFoldSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | k + 1, S => {n | ∃ a ∈ S, ∃ b ∈ kFoldSumset k S, n = a + b}

/--
Erdős Problem 1112 [ErGr80]:

Define $r_k(d_1, d_2)$ to be the smallest integer $r$ (if it exists) such that for any
lacunary sequence $B = \{b_1 < b_2 < \cdots\}$ of positive integers with
$b_{i+1} \geq r \cdot b_i$, there exists a sequence $A = \{a_1 < a_2 < \cdots\}$ of
positive integers with $d_1 \leq a_{i+1} - a_i \leq d_2$ for all $i$, and
$(kA) \cap B = \emptyset$, where $kA$ is the $k$-fold sumset.

Known results:
- $r_2(2,3) = 2$ and $r_2(a,b) \leq 2$ for $a < b$ with $b \neq 2a$
  (Erdős–Graham, Chen).
- $r_3(2,3)$ does not exist: Bollobás, Hegyvári, and Jin showed that for any
  arbitrarily fast growing sequence of lacunary ratios, there exists $B$ such
  that $(A+A+A) \cap B \neq \emptyset$ for all $A$ with gaps in $[2,3]$.
- Further non-existence results by Tang and Yang.
- The general question of existence of $r_k(d_1, d_2)$ for $k \geq 3$ remains open.
-/
@[category research open, AMS 5 11]
theorem erdos_1112 : answer(sorry) ↔
    ∀ (d₁ d₂ : ℕ), 1 ≤ d₁ → d₁ < d₂ →
    ∀ (k : ℕ), 3 ≤ k →
    ∃ (r : ℕ), ∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
      (∀ i, r * B i ≤ B (i + 1)) →
      ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
        (∀ i, d₁ ≤ A (i + 1) - A i) ∧
        (∀ i, A (i + 1) - A i ≤ d₂) ∧
        ∀ n, n ∈ kFoldSumset k (Set.range A) → n ∉ Set.range B := by
  sorry

end Erdos1112
