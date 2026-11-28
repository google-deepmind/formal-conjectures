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
# Naslund's crossing problem

Let $\mathbb{F}$ be a field and let $\mathcal{P}$ consist of the two partitions
$\{\{1, 2\}, \{3, 4\}\}$ and $\{\{1, 3\}, \{2, 4\}\}$ of $\{1, 2, 3, 4\}$. A tensor
$h : [n]^4 \to \mathbb{F}$ has $\mathcal{P}$-rank $1$ if
$h(x_1, x_2, x_3, x_4) = a(x_1, x_2) b(x_3, x_4)$ or
$h(x_1, x_2, x_3, x_4) = c(x_1, x_3) d(x_2, x_4)$. The $\mathcal{P}$-rank of a tensor is the least
number of tensors of $\mathcal{P}$-rank $1$ with that sum [Nas20, Definition 8].

Naslund asks whether the tensor $\delta(x_1, x_4)\delta(x_2, x_3)$ has superlinear
$\mathcal{P}$-rank [Nas20, Problem 12]. He notes that a positive answer would improve lower bounds
for non-commutative circuits. The lower bound $n$ is immediate [Kar23, Question 1.2].

## Matrix form

Index the rows of an $n^2 \times n^2$ matrix by the pairs $(x_1, x_2)$ and the columns by the pairs
$(x_3, x_4)$. The tensor $\delta(x_1, x_4)\delta(x_2, x_3)$ becomes the swap matrix $S_n$. A sum of
$r$ tensors $a(x_1, x_2) b(x_3, x_4)$ is a matrix $B$ of rank at most $r$. A sum of $s$ tensors
$c(x_1, x_3) d(x_2, x_4)$ is a matrix $C$ whose realignment $\mathcal{R}(C)$ has rank at most $s$.
So the $\mathcal{P}$-rank is the least value of
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C)$ over all splittings $S_n = B + C$.
`IsSumOfPRankOne.exists_split` proves the direction that lower bounds need.

The lower bounds below are stated in matrix form, as in their formal proof [Sin26]. They are
linear in $n$, so they do not answer the question.

*References:*
* [Nas20] E. Naslund, *The partition rank of a tensor and $k$-right corners in $\mathbb{F}_q^n$*,
  J. Combin. Theory Ser. A 174 (2020), 105190
  ([arxiv/1701.04475](https://arxiv.org/abs/1701.04475)). Definition 8 and Problem 12.
* [Kar23] T. Karam, *The interplay between bounded ranks of tensors arising from partitions*
  ([arxiv/2310.11356](https://arxiv.org/abs/2310.11356)). Question 1.2 restates the problem.
* [Sin26] A. Singh, *Lower bounds for Naslund's crossing problem*,
  https://github.com/Arth-Singh/crossing-lower-bounds. The paper and the Lean proofs of the
  lower bounds below.
-/

@[expose] public section

namespace Arxiv.«1701.04475»

open Filter Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The tensor $\delta(x_1, x_4)\delta(x_2, x_3)$ on $[n]^4$. -/
def crossing (F : Type*) [Field F] (n : ℕ) : Fin n → Fin n → Fin n → Fin n → F :=
  fun x₁ x₂ x₃ x₄ ↦ if x₁ = x₄ ∧ x₂ = x₃ then 1 else 0

/-- `IsSumOfPRankOne T r s` states that the tensor $T$ on $[n]^4$ is a sum of $r$ tensors
$a(x_1, x_2) b(x_3, x_4)$ and $s$ tensors $c(x_1, x_3) d(x_2, x_4)$. The $\mathcal{P}$-rank of $T$
is the least $r + s$ for which this holds. -/
def IsSumOfPRankOne (T : Fin n → Fin n → Fin n → Fin n → F) (r s : ℕ) : Prop :=
  ∃ (a b : Fin r → Fin n → Fin n → F) (c d : Fin s → Fin n → Fin n → F),
    ∀ x₁ x₂ x₃ x₄, T x₁ x₂ x₃ x₄ = ∑ i, a i x₁ x₂ * b i x₃ x₄ + ∑ j, c j x₁ x₃ * d j x₂ x₄

/-- For $n = 1$ the crossing tensor is the constant $1$, which has $\mathcal{P}$-rank $1$. -/
@[category test, AMS 15]
theorem isSumOfPRankOne_crossing_one : IsSumOfPRankOne (crossing F 1) 1 0 :=
  ⟨fun _ _ _ ↦ 1, fun _ _ _ ↦ 1, fun j ↦ j.elim0, fun j ↦ j.elim0, by
    simp [crossing, Subsingleton.elim _ (0 : Fin 1)]⟩

/--
**Naslund's crossing problem** ([Nas20, Problem 12](https://arxiv.org/pdf/1701.04475#page=8)):
does the tensor $\delta(x_1, x_4)\delta(x_2, x_3)$ on $[n]^4$ have $\mathcal{P}$-rank
$\gg n^{1 + \varepsilon}$ for some $\varepsilon > 0$ as $n$ grows?

The source does not restrict the field, so the statement is for an arbitrary field $\mathbb{F}$.
-/
@[category research open, AMS 15 68, question]
theorem crossing_superlinear (F : Type*) [Field F] :
    ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ r s : ℕ,
      IsSumOfPRankOne (crossing F n) r s → c * (n : ℝ) ^ (1 + ε) ≤ r + s := by
  sorry

/-- The swap matrix $S_n$: the entry in row $(x, y)$ and column $(u, v)$ is $1$ if $u = y$ and
$v = x$, and $0$ otherwise. It is the crossing tensor with rows $(x_1, x_2)$ and columns
$(x_3, x_4)$. -/
def swapMat (F : Type*) [Field F] (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) F :=
  fun p q ↦ if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The realignment $\mathcal{R}(C)$ of a matrix $C$: its entry in row $(x, u)$ and column
$(y, v)$ is the entry of $C$ in row $(x, y)$ and column $(u, v)$. -/
def realign (C : Matrix (Fin n × Fin n) (Fin n × Fin n) F) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) F :=
  fun p q ↦ C (p.1, q.1) (p.2, q.2)

/-- The realignment fixes the swap matrix. -/
@[category test, AMS 15]
theorem realign_swapMat : realign (swapMat F n) = swapMat F n := by
  ext p q
  simp [realign, swapMat, eq_comm]

/-- A decomposition of the crossing tensor into $r$ tensors along $\{\{1, 2\}, \{3, 4\}\}$ and
$s$ tensors along $\{\{1, 3\}, \{2, 4\}\}$ gives a splitting $S_n = B + C$ with
$\operatorname{rank} B \le r$ and $\operatorname{rank} \mathcal{R}(C) \le s$. So a lower bound on
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C)$ over all splittings is a lower bound
on the $\mathcal{P}$-rank. -/
@[category API, AMS 15]
theorem IsSumOfPRankOne.exists_split {r s : ℕ} (h : IsSumOfPRankOne (crossing F n) r s) :
    ∃ B C : Matrix (Fin n × Fin n) (Fin n × Fin n) F,
      swapMat F n = B + C ∧ B.rank ≤ r ∧ (realign C).rank ≤ s := by
  obtain ⟨a, b, c, d, h⟩ := h
  let X : Matrix (Fin n × Fin n) (Fin r) F := fun p i ↦ a i p.1 p.2
  let Y : Matrix (Fin r) (Fin n × Fin n) F := fun i q ↦ b i q.1 q.2
  let Z : Matrix (Fin n × Fin n) (Fin s) F := fun p j ↦ c j p.1 p.2
  let W : Matrix (Fin s) (Fin n × Fin n) F := fun j q ↦ d j q.1 q.2
  refine ⟨X * Y, realign (Z * W), ?_, ?_, ?_⟩
  · ext ⟨x₁, x₂⟩ ⟨x₃, x₄⟩
    have key : swapMat F n (x₁, x₂) (x₃, x₄) = crossing F n x₁ x₂ x₃ x₄ := by
      simp [swapMat, crossing, and_comm, eq_comm]
    rw [key, h x₁ x₂ x₃ x₄]
    rfl
  · exact (rank_mul_le_left X Y).trans ((rank_le_card_width X).trans (by simp))
  · exact (rank_mul_le_left Z W).trans ((rank_le_card_width Z).trans (by simp))

/-- For $n \ge 3$, every splitting $S_n = B + C$ of the swap matrix has
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C) \ge 4n/3$ [Sin26, Theorem 1]. So the
$\mathcal{P}$-rank of the crossing tensor is at least $4n/3$. Equality holds for $n = 3$. -/
@[category research solved, AMS 15, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000011"]
theorem crossing_superlinear.variants.four_thirds (hn : 3 ≤ n)
    (B C : Matrix (Fin n × Fin n) (Fin n × Fin n) F) (h : swapMat F n = B + C) :
    4 * n ≤ 3 * (B.rank + (realign C).rank) := by
  sorry

/-- For $n \ge 5$, every splitting $S_n = B + C$ of the swap matrix has
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C) \ge 15n/11$ [Sin26, Theorem 2]. -/
@[category research solved, AMS 15, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000011"]
theorem crossing_superlinear.variants.fifteen_elevenths (hn : 5 ≤ n)
    (B C : Matrix (Fin n × Fin n) (Fin n × Fin n) F) (h : swapMat F n = B + C) :
    15 * n ≤ 11 * (B.rank + (realign C).rank) := by
  sorry

/-- For $n \ge 7$, every splitting $S_n = B + C$ of the swap matrix has
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C) \ge 67n/49$ [Sin26, Theorem 3]. -/
@[category research solved, AMS 15, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000011"]
theorem crossing_superlinear.variants.sixtyseven_fortyninths (hn : 7 ≤ n)
    (B C : Matrix (Fin n × Fin n) (Fin n × Fin n) F) (h : swapMat F n = B + C) :
    67 * n ≤ 49 * (B.rank + (realign C).rank) := by
  sorry

/-- For $n \ge 4$, every splitting $S_n = B + C$ of the swap matrix has
$\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C) \ge n + 3$ [Sin26, Theorem 4]. This
is the best of the four bounds for $n = 4$ and $n = 5$. -/
@[category research solved, AMS 15, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000011"]
theorem crossing_superlinear.variants.add_three (hn : 4 ≤ n)
    (B C : Matrix (Fin n × Fin n) (Fin n × Fin n) F) (h : swapMat F n = B + C) :
    n + 3 ≤ B.rank + (realign C).rank := by
  sorry

/-- For $n = 4$ the least value of $\operatorname{rank} B + \operatorname{rank} \mathcal{R}(C)$
over all splittings $S_4 = B + C$ is $7$, over every field [Sin26, Corollary 5]. -/
@[category research solved, AMS 15, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000011"]
theorem crossing_superlinear.variants.four_eq_seven (F : Type*) [Field F] :
    (∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C ∧ B.rank + (realign C).rank = 7) ∧
    ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C → 7 ≤ B.rank + (realign C).rank := by
  sorry

end Arxiv.«1701.04475»
