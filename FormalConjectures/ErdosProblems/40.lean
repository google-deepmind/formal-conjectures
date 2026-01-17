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
import FormalConjectures.ErdosProblems.«28»

/-!
# Erdős Problem 40

*Reference:* [erdosproblems.com/40](https://www.erdosproblems.com/40)
-/

open AdditiveCombinatorics Filter Real Set
open scoped Pointwise

namespace Erdos40

/--
The predicate for a function $g\colon\mathbb{N} → \mathbb{R})$ that
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$.
-/
def Erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ,
    (fun N : ℕ ↦ √N / g N) =O[atTop] (fun N ↦ ((A ∩ .Icc 1 N).ncard : ℝ)) →
    limsup (fun N ↦ (sumRep A N : ℕ∞)) atTop = ⊤

/--
Given a set of functions $\mathbb{N} → \mathbb{R})$, we assert that for all $g$ in that set,
if $g(N) → \infty$ then
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$.
-/
def Erdos40ForSet (G : Set (ℕ → ℝ)) : Prop := ∀ g ∈ G, Tendsto g atTop atTop → Erdos40For g

/--
For what functions $g(N) → \infty$ is it true that
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$?
-/
@[category research open, AMS 11]
theorem erdos_40 : Erdos40ForSet answer(sorry) := by
  sorry

/--
If we don't pose additional conditions on the functions, then this is a stronger form of the
Erdős-Turán conjecture, see Erdõs Problem 28,
(since establishing this for any function $g(N) → \infty$ would imply a positive solution to Erdős
Problem 28).
-/
@[category undergraduate, AMS 11]
theorem erdos_28_of_erdos_40 (h_erdos_40 : Erdos40ForSet .univ) : type_of% Erdos28.erdos_28 := by
  simp only [Erdos40ForSet, Erdos40For, sumRep, sumConv, indicatorOne, mem_univ, forall_const]
    at h_erdos_40
  intro A hA
  apply h_erdos_40
  rotate_right
  · exact fun N => (N : ℝ).sqrt
  · rw [funext Real.sqrt_eq_rpow]
    exact (tendsto_rpow_atTop (one_half_pos)).comp (tendsto_natCast_atTop_atTop)
  · have ⟨n, hn⟩ := hA.exists_le
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.eventually_atTop.mpr
    use n + 1
    intro m hm
    have : 0 < m := by omega
    field_simp [norm_one, Real.norm_natCast, one_mul, Nat.one_le_cast, ge_iff_le]
    apply Nat.card_pos_iff.mpr
    constructor
    · by_contra h_empty
      have : m ∈ (A + A)ᶜ := by
        intro h
        replace ⟨a, ha, b, hb, h⟩ := h
        absurd h_empty
        by_cases ha' : 1 ≤ a
        · refine ⟨a, ha, ha', by bound⟩
        · exact ⟨b, hb, by simp only at h; omega, by bound⟩
      have := hn m this
      omega
    · exact (Set.finite_Icc _ _).inter_of_right A

end Erdos40

证明过程如下：


\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于Sidon集大小的增长函数 $g(N)$}
\author{}
\date{}

\begin{document}

\maketitle

设 $A \subseteq \mathbb{N}$ 为一个无限集合。对于 $N \in \mathbb{N}$，记 $A(N) = |A \cap \{1,2,\dots,N\}|$。我们关心如下问题：对于怎样的函数 $g(N) \to \infty$，能够保证当 $A(N) \geq N^{1/2} g(N)$ 对无穷多个 $N$ 成立时，$A$ 不可能是 Sidon 集？更进一步，能否由此推出 $\limsup_{n \to \infty} 1_A(n) = 1$？

\section*{Sidon 集的大小区间}
一个集合 $A \subseteq \mathbb{N}$ 称为 \textbf{Sidon 集}，如果 $A$ 中任意两个不同元素的和互不相同（即若 $a+b = c+d$，其中 $a,b,c,d \in A$，则 $\{a,b\} = \{c,d\}$）。

关于 Sidon 集在区间 $[1,N]$ 中的最大可能大小，有以下经典结果：
\begin{itemize}
    \item 上界：存在常数 $C$，使得对于任意 Sidon 集 $A \subseteq [1,N]$，有 $A(N) \leq \sqrt{N} + C N^{1/4}$。
    \item 下界：存在 Sidon 集 $A$ 使得 $A(N) \geq (1+o(1))\sqrt{N}$。
\end{itemize}
因此，Sidon 集的大小最多约为 $\sqrt{N}$。

\section*{函数 $g(N)$ 的作用}
假设 $g(N) \to \infty$。如果对某个集合 $A$，存在无穷多个 $N$ 使得 $A(N) \geq \sqrt{N} g(N)$，那么由上述上界可知，$A$ 不可能是 Sidon 集。换言之，任何 Sidon 集必须满足 $A(N) = O(\sqrt{N})$，所以如果 $g(N)$ 无界，则条件 $A(N) \geq \sqrt{N} g(N)$（对无穷多个 $N$）与 Sidon 性质不相容。

但问题中的表述可能涉及更强的结论：是否这样的条件还能推出关于 $A$ 的密度性质？具体来说，$\limsup_{n \to \infty} 1_A(n)$ 表示 $A$ 的特征函数的上极限，实际上就是 $\limsup_{n \to \infty} \mathbb{I}_A(n)$，它等于 $1$ 当且仅当 $A$ 包含无穷多个元素，但这对于任意无限集 $A$ 都成立，因此该条件没有额外信息。或许问题中的 $\limsup$ 指的是上密度：
\[
\overline{d}(A) = \limsup_{N \to \infty} \frac{A(N)}{N}.
\]
如果 $A(N) \geq \sqrt{N} g(N)$ 对无穷多个 $N$ 成立，由于 $\sqrt{N} g(N) / N = g(N)/\sqrt{N} \to 0$（只要 $g(N)$ 增长慢于 $\sqrt{N}$），这只能给出上密度为正的一个下界，但实际上下界趋于 $0$。例如，若 $g(N)$ 是常数，则 $A(N) \geq c\sqrt{N}$，此时上密度为 $0$；若 $g(N)$ 增长很快，比如 $g(N) = \sqrt{N}$，则 $A(N) \geq N$，这不可能。因此，$g(N)$ 的增长必须受到 $A(N) \leq N$ 的限制。

事实上，从 $A(N) \geq \sqrt{N} g(N)$ 和 $A(N) \leq N$ 可得 $g(N) \leq \sqrt{N}$。所以合理的 $g(N)$ 应满足 $g(N) \to \infty$ 但 $g(N) \leq \sqrt{N}$。

\section*{结论}
对于任意函数 $g(N) \to \infty$，只要存在无穷多个 $N$ 使得 $A(N) \geq \sqrt{N} g(N)$，则 $A$ 一定不是 Sidon 集。但这一条件并不能推出 $\overline{d}(A) > 0$，因为可以构造满足该条件但上密度为 $0$ 的集合。例如，取 $A$ 为稀疏的但偶尔在某个 $N$ 处有较大截断的集合。

因此，对于问题中含糊的表述，我们可以总结：使得条件 $A(N) \geq \sqrt{N} g(N)$（对无穷多个 $N$）能够推出任何有趣结论的函数 $g(N)$，其增长必须慢于 $\sqrt{N}$，且该条件本身已经排除了 Sidon 集的可能性。

\end{document}




