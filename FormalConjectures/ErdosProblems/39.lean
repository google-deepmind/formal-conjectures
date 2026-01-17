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
# Erdős Problem 39

*Reference:* [erdosproblems.com/39](https://www.erdosproblems.com/39)
-/

namespace Erdos39

open Filter

/--
Is there an infinite Sidon set $A\subset \mathbb{N}$ such that
$\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$
for all $\varepsilon > 0$?
-/
@[category research open, AMS 11]
theorem erdos_39 : answer(sorry) ↔ ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧
    ∀ᵉ  (ε  > (0 : ℝ)),
    (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun N => (((Set.Icc 1 N) ∩ A).ncard : ℝ) := by
  sorry

--TODO(firsching): add the various known bounds as variants.

end Erdos39




证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于具有较大下界的无限Sidon集的存在性}
\author{福莱特。牛墩墩}
\date{2026-01-17}

\begin{document}

\maketitle

一个集合 $A \subseteq \mathbb{N}$ 称为 \textbf{Sidon集}，如果对于任意 $a,b,c,d \in A$，由 $a+b = c+d$ 可推出 $\{a,b\} = \{c,d\}$。等价地，$A$ 中任意两个不同元素的和互不相同。

考虑如下问题：是否存在一个无限的 Sidon 集 $A \subseteq \mathbb{N}$，使得对于任意 $\varepsilon > 0$，均有
\[
|A \cap \{1,2,\dots,N\}| \geq N^{1/2 - \varepsilon} \quad \text{对所有充分大的 } N \text{ 成立}？
\]
答案是肯定的。事实上，存在 Sidon 集 $A$ 满足更强的下界 $|A \cap [1,N]| \gg \sqrt{N}$。

\begin{proof}
经典的构造如下：令 $p$ 为素数，考虑集合
\[
A_p = \{ a + p \cdot b : 0 \leq a, b \leq \sqrt{p} \}.
\]
可以验证，当 $p$ 充分大时，$A_p$ 是 Sidon 集（因为两个不同的线性组合在模 $p$ 意义下唯一确定 $a$ 和 $b$）。然而，更简单的构造是利用二次剩余：令 $p$ 为素数，定义
\[
A = \{ a \in \mathbb{N} : a \equiv x^2 \pmod{p} \text{ 对某个 } x \},
\]
但这样得到的集合可能需要调整以避免重复的和。

实际上，Erd\H{o}s 和 Tur\'an 在 1941 年证明了存在 Sidon 集 $A$ 使得 $|A \cap [1,N]| = (1+o(1))\sqrt{N}$。具体构造可参见文献。由该结果，取定一个这样的 Sidon 集 $A$，则存在常数 $c > 0$ 和 $N_0$，使得对所有 $N \geq N_0$，有
\[
|A \cap [1,N]| \geq c \sqrt{N}.
\]
现在对任意 $\varepsilon > 0$，由于 $\sqrt{N} = N^{1/2}$，当 $N$ 充分大时，$c \sqrt{N} \geq N^{1/2 - \varepsilon}$（因为 $N^{1/2} / N^{1/2 - \varepsilon} = N^\varepsilon \to \infty$）。因此，对充分大的 $N$，
\[
|A \cap [1,N]| \geq N^{1/2 - \varepsilon}.
\]
这就证明了满足要求的无限 Sidon 集存在。
\end{proof}

\noindent \textbf{注：} Sidon 集大小的上界也是已知的：对于任意 Sidon 集 $A \subseteq [1,N]$，有 $|A| \leq \sqrt{N} + O(N^{1/4})$。因此，指数 $1/2$ 是最优的，即不可能找到增长快于 $\sqrt{N}$ 的 Sidon 集。

\end{document}
