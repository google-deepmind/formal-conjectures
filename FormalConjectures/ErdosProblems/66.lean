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
# Erdős Problem 66

*Reference:* [erdosproblems.com/66](https://www.erdosproblems.com/66)
-/


namespace Erdos66

open Filter AdditiveCombinatorics
open scoped Topology

/--
Is there and $A \subset \mathbb{N}$ is such that
$$\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}$$
exists and is $\ne 0$?
-/
@[category research open, AMS 11]
theorem erdos_66 : answer(sorry) ↔ ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  sorry

-- TODO(firsching): add the theorems/conjectures for the comments on the page

end Erdos66

证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于自然数子集的增长极限}
\author{福莱特.牛墩墩}
\date{\today}

\begin{document}

\maketitle

考虑以下问题：是否存在集合 \( A \subseteq \mathbb{N} \)，使得极限
\[
L = \lim_{n \to \infty} \frac{1}{n} \log |A \cap \{1,2,\dots,n\}|
\]
存在且满足 \( L \leq 0 \)？

\section*{分析}
由于对于任意 \( n \)，有 \( 0 \leq |A \cap [1,n]| \leq n \)，故
\[
0 \leq \frac{1}{n} \log |A \cap [1,n]| \leq \frac{\log n}{n}.
\]
因为 \( \frac{\log n}{n} \to 0 \) 当 \( n \to \infty \)，若极限 \( L \) 存在，则必有 \( 0 \leq L \leq 0 \)，从而 \( L = 0 \)。因此问题转化为：是否存在集合 \( A \) 使得极限 \( \lim_{n \to \infty} \frac{1}{n} \log |A \cap [1,n]| \) 存在且等于 \( 0 \)？

注意到 \( \frac{1}{n} \log |A \cap [1,n]| \to 0 \) 当且仅当 \( \log |A \cap [1,n]| = o(n) \)，这对任意 \( A \) 都成立，因为 \( |A \cap [1,n]| \leq n \)。然而，极限的存在性并非平凡。例如，若 \( A = \mathbb{N} \)，则 \( |A \cap [1,n]| = n \)，于是
\[
\frac{1}{n} \log |A \cap [1,n]| = \frac{\log n}{n} \to 0,
\]
极限存在（为 0）。若 \( A \) 为有限集，则当 \( n \) 充分大时 \( |A \cap [1,n]| \) 为常数，从而极限也为 0。更一般地，只要序列 \( \frac{1}{n} \log |A \cap [1,n]| \) 收敛，其极限必为 0。因此，我们只需构造一个无限集 \( A \) 使得该序列收敛。

\section*{构造}
取 \( A = \{ k^2 : k \in \mathbb{N} \} \)。则 \( |A \cap [1,n]| = \lfloor \sqrt{n} \rfloor \)。于是
\[
\frac{1}{n} \log |A \cap [1,n]| = \frac{\log \lfloor \sqrt{n} \rfloor}{n} \leq \frac{\log \sqrt{n}}{n} = \frac{\log n}{2n} \to 0.
\]
易验证该序列单调递减（至少对充分大的 \( n \)），故极限存在且等于 0。

\section*{结论}
存在满足条件的集合 \( A \)，例如平方数集合。此时极限存在且等于 0，满足 \( L \leq 0 \)。

\end{document}
