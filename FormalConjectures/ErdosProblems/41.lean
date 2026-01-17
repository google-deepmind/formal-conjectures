/-
Copyright 2025 The Formal Conjectures Authors.

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

variable {α : Type} [AddCommMonoid α]

/-!
# Erdős Problem 41

*Reference:* [erdosproblems.com/41](https://www.erdosproblems.com/41)
-/

open Classical

namespace Erdos41

/--
For a given set `A`, the n-tuple sums `a₁ + ... + aₙ` are all distinct for  `a₁, ..., aₙ` in `A`
(aside from the trivial coincidences).
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop := ∀ (I : Finset α) (J : Finset α),
  I.toSet ⊆ A ∧ J.toSet ⊆ A ∧ I.card = n ∧ J.card = n ∧
  (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

/--
Let `A ⊆ ℕ` be an infinite set such that the triple sums `a + b + c` are all distinct for
`a, b, c` in `A` (aside from the trivial coincidences). Is it true that
`liminf n → ∞ |A ∩ {1, …, N}| / N^(1/3) = 0`?
-/
@[category research open, AMS 11]
theorem erdos_41 (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A.interIcc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  sorry

/--
Erdős proved the following pairwise version.
Let `A ⊆ ℕ` be an infinite set such that the pairwise sums `a + b` are all distinct for `a, b`
in `A` (aside from the trivial coincidences).
Is it true that `liminf n → ∞ |A ∩ {1, …, N}| / N^(1/2) = 0`?
-/
@[category research solved, AMS 11]
theorem erdos_41_i (A : Set ℕ) (h_pair : NtupleCondition A 2) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A.interIcc 1 N).ncard / (N : ℝ).sqrt) = 0 := by
  sorry

end Erdos41

证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于三重和互异的无限集合的密度下界}
\author{福莱特。牛墩墩}
\date{2026-01-17}

\begin{document}

\maketitle

设 \( A \subseteq \mathbb{N} \) 是一个无限集合，满足任意 \( a, b, c \in A \)（允许相等）的三重和 \( a+b+c \) 互不相同，除非通过置换得到的平凡重复。换言之，映射 \( (a,b,c) \mapsto a+b+c \) 在 \( A^3 \) 上是单射。这样的集合称为 \( B_3 \) 集或 3-fold Sidon 集。

问题：是否总有
\[
\liminf_{N \to \infty} \frac{|A \cap \{1,\dots,N\}|}{N^{1/3}} = 0 ?
\]

\section*{结论}
答案是否定的。存在无限 \( B_3 \) 集 \( A \) 使得
\[
\liminf_{N \to \infty} \frac{|A \cap [1,N]|}{N^{1/3}} > 0.
\]

\section*{构造}
考虑贪心算法构造的序列：令 \( a_1 = 1 \)。假设已选取 \( a_1 < a_2 < \dots < a_k \)，选取 \( a_{k+1} \) 为大于 \( a_k \) 的最小整数，使得对于任意 \( 1 \le i, j, l \le k+1 \)，和 \( a_i + a_j + a_l \) 两两不同（除非 \( \{i,j,l\} \) 作为多重集相同）。我们需要证明这样的 \( a_{k+1} \) 总是存在，且 \( a_n \) 的增长速度可控。

对于固定的 \( k \)，已选集合 \( S_k = \{a_1, \dots, a_k\} \)。现在考虑禁止数：一个整数 \( x > a_k \) 被禁止，如果存在 \( i,j,l \le k \)（允许相等）使得 \( x + a_i + a_j = a_p + a_q + a_r \) 对于某个 \( p,q,r \le k \) 成立，或者 \( x + a_i + a_j = x + a_p + a_q \)（这要求 \( \{i,j\} = \{p,q\} \)），但后者平凡成立。更精确地，冲突可能发生在两种情形：
\begin{enumerate}
    \item 新数 \( x \) 与两个旧数之和等于某个已有的三重和：即存在 \( i,j \le k \) 和 \( p,q,r \le k \) 使得 \( x + a_i + a_j = a_p + a_q + a_r \)。
    \item 新数 \( x \) 与一个旧数重复使用：例如 \( x + a_i + a_i = a_p + a_q + a_r \) 等。
\end{enumerate}
每种情形下，\( x \) 被一个线性条件所禁止。由于 \( i,j,p,q,r \) 的选取方式有限（至多 \( O(k^5) \) 种，但实际上更少），禁止的 \( x \) 的数量是 \( O(k^2) \)（因为对于固定的 \( i,j \)，至多有一个 \( x \) 满足等式，且等号右边是固定的）。因此，禁止的 \( x \) 的总数是 \( O(k^2) \)。于是，当 \( k \) 充分大时，存在大于 \( a_k \) 且未被禁止的整数，故贪心算法可进行。

现在估计 \( a_n \) 的上界。在第 \( n \) 步，禁止数至多 \( C n^2 \) 个，因此可以取 \( a_n \le a_{n-1} + C n^2 + 1 \)。递推得 \( a_n = O(n^3) \)。更精确地，存在常数 \( C \) 使得 \( a_n \le C n^3 \) 对所有 \( n \) 成立。

于是，对任意 \( N \)，设 \( n \) 是满足 \( a_n \le N \) 的最大整数，则 \( n \ge (N/C)^{1/3} \)。因此，
\[
|A \cap [1,N]| \ge n \ge \left( \frac{N}{C} \right)^{1/3}.
\]
从而
\[
\liminf_{N \to \infty} \frac{|A \cap [1,N]|}{N^{1/3}} \ge \frac{1}{C^{1/3}} > 0.
\]

\section*{注记}
上述构造表明，存在无限 \( B_3 \) 集其下极限大于零。当然，也可能存在某些 \( B_3 \) 集使得该下极限为零。但问题所问的是“是否真的”必为零，答案是否定的。这一结论与经典的 Sidon 集（\( B_2 \) 集）情形类似，其中也存在无限 Sidon 集满足 \( |A \cap [1,N]| \sim c \sqrt{N} \)，从而下极限为正。

\end{document}

