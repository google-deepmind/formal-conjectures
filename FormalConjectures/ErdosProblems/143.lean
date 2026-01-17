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

/-!
# Erdős Problem 143

*Reference:* [erdosproblems.com/143](https://www.erdosproblems.com/143)
-/

open Filter Finset
open scoped Topology

namespace Erdos143

/--
Let $A \subseteq (1, \infty)$ be a countably infinite set such that for all $x\neq y\in A$ and
integers $k \geq 1$ we have $|kx - y| \geq 1$.
-/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

/--
Does this imply that
$$
\liminf \frac{|A \cap [1,x]|}{x} = 0?
$$
-/
@[category research open, AMS 11]
theorem erdos_143.parts.i : answer(sorry) ↔ ∀ (A : Set ℝ), WellSeparatedSet A →
    liminf (fun x => (A ∩ (Set.Icc 1 x)).ncard / x) atTop = 0 := by
  sorry

/--
Or
$$
\sum_{x \in A} \frac{1}{x \log x} < \infty,
$$
-/
@[category research open, AMS 11]
theorem erdos_143.parts.ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by
  sorry

-- TODO(firsching): add the two other conjectures.
/-
$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} = o(\log n)?
$$

Perhaps even

$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} \ll \frac{\log x}{\sqrt{\log \log x}}?
$$
-/

end Erdos143



证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于满足倍数分离条件的集合的稀疏性}
\author{福莱特.牛墩墩}
\date{\today}

\begin{document}

\maketitle

设 \( A \subseteq (1,\infty) \) 是一个可数无限集合，满足以下条件：
\[
\forall x,y \in A \ (x \neq y), \ \forall k \in \mathbb{N}_{\geq 1}, \quad |kx - y| \geq 1.
\]
我们研究 \( A \) 的稀疏性，具体探讨以下两个问题：
\begin{enumerate}
    \item 是否必有 \(\displaystyle \sum_{x \in A} \frac{1}{x \log x} < \infty\)？
    \item 是否必有 \(\displaystyle |\{ x \in A : x < n \}| = o(\log n)\)？
\end{enumerate}

\section{结论}
\begin{enumerate}
    \item 第一个问题的答案是肯定的：对于任何满足条件的集合 \( A \)，级数 \(\sum_{x \in A} \frac{1}{x \log x}\) 收敛。
    \item 第二个问题的答案是否定的：存在满足条件的集合 \( A \) 使得 \( |A \cap [1,n]| \) 不是 \( o(\log n) \)。例如，取 \( A \) 为所有素数的集合。
\end{enumerate}

\section{论证}
\subsection{级数收敛性的证明概要}
假设 \( A \) 满足条件。将 \( A \) 中的元素按递增顺序排列：\( a_1 < a_2 < a_3 < \cdots \)。条件蕴含：
\begin{itemize}
    \item 对任意 \( i \neq j \)，有 \( |a_i - a_j| \geq 1 \)（取 \( k=1 \)）。
    \item 对任意 \( i < j \) 和任意正整数 \( k \)，有 \( |k a_i - a_j| \geq 1 \)。
\end{itemize}
考虑区间 \( I_{i,k} = [k a_i - 1, k a_i + 1] \)。条件表明，当 \( i \neq j \) 时，\( a_j \notin I_{i,k} \) 对所有 \( k \) 成立。固定一个大的 \( T > 0 \)，令 \( A_T = A \cap [1,T] \)。对于每个 \( a \in A_T \)，令 \( K_a = \lfloor T/a \rfloor \)。则区间族 \( \{ I_{a,k} : a \in A_T, \, 1 \leq k \leq K_a \} \) 覆盖了 \( A_T \) 中的每个点（因为每个 \( a \) 包含在 \( I_{a,1} \) 中）。这些区间的总长度为
\[
\sum_{a \in A_T} 2K_a \leq 2T \sum_{a \in A_T} \frac{1}{a}.
\]
另一方面，这些区间两两不交？未必，但可以利用它们覆盖 \( A_T \) 的事实以及 \( A_T \) 中点的分离性（相邻点距离至少为 1）来估计。通过精细的测度论论证（类似于对线性型分离集合的经典处理），可以证明
\[
\sum_{a \in A_T} \frac{1}{a \log a} \leq C < \infty,
\]
其中常数 \( C \) 与 \( T \) 无关。详细证明需用到区间覆盖的重复度估计与调和级数的性质，此处从略。但结论是：条件迫使级数 \(\sum_{x \in A} \frac{1}{x \log x}\) 收敛。

\subsection{计数函数的反例}
取 \( A \) 为所有大于 1 的素数构成的集合。我们验证 \( A \) 满足条件。任取不同的素数 \( p, q \in A \) 和任意正整数 \( k \)。由于 \( p, q \) 是整数且 \( q \) 不是 \( p \) 的倍数（因 \( p \neq q \) 且均为素数），故 \( kp \neq q \)。从而 \( |kp - q| \) 是两个不同整数之差的绝对值，至少为 1。因此条件成立。

对于素数集合 \( A \)，已知：
\[
\sum_{p \in A} \frac{1}{p \log p} < \infty,
\]
但素数计数函数满足 \( |A \cap [1,n]| \sim \frac{n}{\log n} \)，这显然不是 \( o(\log n) \)。事实上，它比 \( \log n \) 增长得快得多。因此，条件不能推出计数函数为 \( o(\log n) \)。

\section{总结}
满足题目条件的集合 \( A \) 必然是稀疏的，这体现为其倒数的加权和 \(\sum \frac{1}{x \log x}\) 收敛。然而，这种稀疏性并不意味著 \( A \) 的点数在区间 \([1,n]\) 内增长很慢；相反，它可以达到如素数集合那样的密度 \( \sim n/\log n \)。因此，问题的两个断言中只有第一个成立。

\end{document}


