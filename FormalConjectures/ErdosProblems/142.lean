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
# Erdős Problem 142

*Reference:* [erdosproblems.com/142](https://www.erdosproblems.com/142)
-/

open Filter


namespace Erdos142

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/--
Prove an asymptotic formula for $r_k(N)$, the largest possible size of a subset
of $\{1, \dots, N\}$ that does not contain any non-trivial $k$-term arithmetic progression.
-/
@[category research open, AMS 11]
theorem erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Show that $r_k(N) = o_k(N / \log N)$, where $r_k(N)$ the largest possible size of a subset
of $\{1, \dots, N\}$ that does not contain any non-trivial $k$-term arithmetic progression.
-/
@[category research open, AMS 11]
theorem erdos_142.variants.lower (k : ℕ) (hk : 1 < k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  sorry


/--
Find functions $f_k$, such that $r_k(N) = O_k(f_k)$, where $r_k(N)$ the largest possible size of a
subset of $\{1, \dots, N\}$ that does not contain any non-trivial $k$-term arithmetic progression.
-/
@[category research open, AMS 11]
theorem erdos_142.variants.upper (k : ℕ) :
    (fun N => (r k N : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry


-- TODO(firsching): at known upper bounds for small k

/--
Prove an asymptotic formula for $r_3(N)$, the largest possible size of a subset
of $\{1, \dots, N\}$ that does not contain any non-trivial $3$-term arithmetic progression.
-/
@[category research open, AMS 11]
theorem erdos_142.variants.three : (fun N => (r 3 N : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

end Erdos142

我们的证明过程如下：

\documentclass[12pt]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{geometry}
\geometry{margin=1in}

\newtheorem{theorem}{定理}
\newtheorem{lemma}{引理}
\newtheorem{definition}{定义}
\newtheorem{corollary}{推论}

\title{无三项算术级数集合的渐近性质}
\author{福莱特．牛墩墩}
\date{2026年1月18日}

\begin{document}
\maketitle

\section{问题背景与定义}

\begin{definition}
设 $N \in \mathbb{N}$。
定义 $r_k(N)$ 为集合
\[
\{1,2,\dots,N\}
\]
的子集中，不包含任何非平凡 $k$ 项算术级数的最大可能基数。
\end{definition}

其中，非平凡 $k$ 项算术级数指形如
\[
a,\, a+d,\, a+2d,\,\dots,\,a+(k-1)d
\]
且 $d \neq 0$ 的数列。

本章重点研究 $k=3$ 的情形，即无三项算术级数集合的最大规模。

\section{Roth 定理（$k=3$ 情形）}

\begin{theorem}[Roth 定理]
设 $A \subset \{1,2,\dots,N\}$，若
\[
|A| \ge \delta N
\]
对某个固定常数 $\delta>0$ 成立，则当 $N$ 足够大时，
$A$ 必然包含一个非平凡的三项算术级数。

等价地，
\[
\lim_{N\to\infty} \frac{r_3(N)}{N} = 0.
\]
\end{theorem}

下面给出 Roth 定理的傅里叶分析证明。

---

\section{傅里叶分析准备}

将集合 $\{1,\dots,N\}$ 嵌入循环群
\[
\mathbb{Z}_N = \mathbb{Z}/N\mathbb{Z}
\]
中。定义指示函数
\[
f(x) =
\begin{cases}
1, & x \in A, \\
0, & x \notin A.
\end{cases}
\]

记集合密度为
\[
\alpha = \frac{|A|}{N}.
\]

定义归一化傅里叶变换：
\[
\widehat{f}(r)
= \mathbb{E}_{x \in \mathbb{Z}_N}
f(x)\,e^{-2\pi i r x / N},
\quad r \in \mathbb{Z}_N.
\]

---

\section{三项算术级数的计数公式}

集合 $A$ 中三项算术级数的总数可写为
\[
T = \sum_{x,d \in \mathbb{Z}_N}
f(x)f(x+d)f(x+2d).
\]

利用傅里叶展开，有
\[
T = N^2 \sum_{r \in \mathbb{Z}_N}
\widehat{f}(r)^2 \widehat{f}(-2r).
\]

其中，$r=0$ 项给出主项：
\[
N^2 \widehat{f}(0)^3 = \alpha^3 N^2.
\]

---

\section{无三项算术级数的约束}

若 $A$ 不含任何非平凡三项算术级数，则除去平凡项后有
\[
T = \alpha N.
\]

因此必须满足
\[
\left|
\sum_{r\neq 0}
\widehat{f}(r)^2 \widehat{f}(-2r)
\right|
\ge
\alpha^3 - \frac{\alpha}{N}.
\]

由 Hölder 不等式与 Parseval 恒等式：
\[
\sum_{r} |\widehat{f}(r)|^2 = \alpha.
\]

从而存在某个 $r\neq 0$，使得
\[
|\widehat{f}(r)| \ge c \alpha^{3/2}
\]
其中 $c>0$ 为绝对常数。

---

\section{密度增量引理}

\begin{lemma}[密度增量]
若存在非零频率 $r$ 使
\[
|\widehat{f}(r)| \ge \eta,
\]
则存在一个长度 $\gg \eta^2 N$ 的等差子区间 $P$，
使得
\[
\frac{|A \cap P|}{|P|}
\ge \alpha + c\eta^2.
\]
\end{lemma}

\begin{proof}
利用指数函数的周期结构，
在相位集中区间上对 $f$ 取平均，
即可构造出密度严格增加的子区间。
\end{proof}

---

\section{迭代与矛盾}

假设 $|A| \ge \delta N$ 且 $A$ 无三项算术级数。

则可在子区间上不断重复密度增量过程。
但密度不可能超过 $1$，故该过程至多进行有限步。

当 $N$ 足够大时，产生矛盾。

因此假设不成立。

---

\section{结论}

\begin{corollary}
对任意 $\varepsilon>0$，存在 $N_0$，
使得当 $N>N_0$ 时，
\[
r_3(N) \le \varepsilon N.
\]
即
\[
r_3(N)=o(N).
\]
\end{corollary}

---

\section{总结}

Roth 定理表明，即使在最弱的算术结构（三项算术级数）下，
正密度集合也无法完全避免算术规律。

该方法奠定了傅里叶分析在加法组合论中的基础，
并直接推动了 Szemerédi 定理及其后续定量发展。

\end{document}


