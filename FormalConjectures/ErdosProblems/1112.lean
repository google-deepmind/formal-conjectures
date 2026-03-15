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
theory_. Monographies de L'Enseignement Mathématique (1980), p. 18.

[BHJ97] Bollobás, B., Hegyvári, N., Jin, G., _On a problem of Erdős and Graham_. Discrete
Mathematics (1997), 253–257.

[Ch00] Chen, Y.-G., _On sums and intersects of sequences_. Discrete Mathematics (2000), 351–354.

[TaYa21] Tang, M., Yang, Q.-H., _On a problem of Erdős and Graham_. Publicationes Mathematicae
Debrecen (2021), 485–493.
-/

namespace Erdos1112

/-- The $k$-fold sumset of a set $S$ of natural numbers: all sums $s_1 + \cdots + s_k$
with each $s_i \in S$. Defined recursively: $0S = \{0\}$,
$(k+1)S = \{a + b \mid a \in S,\, b \in kS\}$. -/
def kFoldSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | k + 1, S => {n | ∃ a ∈ S, ∃ b ∈ kFoldSumset k S, n = a + b}

/--
Erdős Problem 1112 [ErGr80, p. 18]:

Define $r_k(d_1, d_2)$ to be the smallest integer $r$ (if it exists) such that for any
lacunary sequence $B = \{b_1 < b_2 < \cdots\}$ of positive integers with
$b_{i+1} \geq r \cdot b_i$, there exists a sequence $A = \{a_1 < a_2 < \cdots\}$ of
positive integers with $d_1 \leq a_{i+1} - a_i \leq d_2$ for all $i$, and
$(kA) \cap B = \emptyset$, where $kA$ is the $k$-fold sumset.

The universal statement — that $r_k(d_1, d_2)$ exists for all $1 \leq d_1 < d_2$ and
$k \geq 3$ — is false. Bollobás, Hegyvári, and Jin [BHJ97] showed that $r_3(2,3)$ does
not exist, so the answer is `False`.
-/
@[category research solved, AMS 5 11]
theorem erdos_1112 : answer(False) ↔
    ∀ (d₁ d₂ : ℕ), 1 ≤ d₁ → d₁ < d₂ →
    ∀ (k : ℕ), 3 ≤ k →
    ∃ (r : ℕ), ∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
      (∀ i, r * B i ≤ B (i + 1)) →
      ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
        (∀ i, d₁ ≤ A (i + 1) - A i) ∧
        (∀ i, A (i + 1) - A i ≤ d₂) ∧
        ∀ n, n ∈ kFoldSumset k (Set.range A) → n ∉ Set.range B := by
  sorry

/--
$r_3(2,3)$ does not exist [BHJ97]: for any ratio $r$, there exists a lacunary sequence $B$
with $b_{i+1} \geq r \cdot b_i$ such that $(A + A + A) \cap B \neq \emptyset$ for every
sequence $A$ with gaps in $[2,3]$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1112.variants.r3_2_3_nonexistence :
    ∀ (r : ℕ), ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, r * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, 2 ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ 3) →
        ∃ n, n ∈ kFoldSumset 3 (Set.range A) ∧ n ∈ Set.range B := by
  sorry

/--
$r_2(a, b) \leq 2$ for all integers $1 \leq a < b$ with $b \neq 2a$ [Ch00]: the $2$-fold
sumset of a sequence with gaps in $[a, b]$ can always avoid any lacunary sequence with
ratio $\geq 2$, provided $b \neq 2a$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1112.variants.r2_upper (a b : ℕ) (ha : 1 ≤ a) (hab : a < b)
    (hne : b ≠ 2 * a) :
    ∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
      (∀ i, 2 * B i ≤ B (i + 1)) →
      ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
        (∀ i, a ≤ A (i + 1) - A i) ∧
        (∀ i, A (i + 1) - A i ≤ b) ∧
        ∀ n, n ∈ kFoldSumset 2 (Set.range A) → n ∉ Set.range B := by
  sorry

/--
$r_2(2, 3) = 2$ [ErGr80], [BHJ97]: the smallest lacunary ratio ensuring avoidance for
$2$-fold sumsets with gaps in $[2, 3]$ is exactly $2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1112.variants.r2_2_3 :
    (∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
      (∀ i, 2 * B i ≤ B (i + 1)) →
      ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
        (∀ i, 2 ≤ A (i + 1) - A i) ∧
        (∀ i, A (i + 1) - A i ≤ 3) ∧
        ∀ n, n ∈ kFoldSumset 2 (Set.range A) → n ∉ Set.range B) ∧
    (∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, 1 * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, 2 ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ 3) →
        ∃ n, n ∈ kFoldSumset 2 (Set.range A) ∧ n ∈ Set.range B) := by
  sorry

/--
$r_2(a, 2a) \geq 2$ for all positive integers $a$ [Ch00]: for any sequence with gaps in
$[a, 2a]$, a lacunary sequence with ratio $1$ (i.e., no lacunary growth requirement) can
intersect its $2$-fold sumset.
-/
@[category research solved, AMS 5 11]
theorem erdos_1112.variants.r2_2a_lower (a : ℕ) (ha : 1 ≤ a) :
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, 1 * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, a ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ 2 * a) →
        ∃ n, n ∈ kFoldSumset 2 (Set.range A) ∧ n ∈ Set.range B := by
  sorry

end Erdos1112
