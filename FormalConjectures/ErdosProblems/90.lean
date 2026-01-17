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
# Erdős Problem 90: The unit distance problem

*Reference:* [erdosproblems.com/90](https://www.erdosproblems.com/90)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos90
open Finset

/--
Given a finite set of points, this function counts the number of **unordered pairs** of distinct
points that are at a distance of exactly 1 from each other.
-/
noncomputable def unitDistancePairsCount (points : Finset ℝ²) : ℕ :=
  (points.offDiag.filter (fun p => dist p.1 p.2 = 1)).card / 2


/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount points | (points : Finset ℝ²) (_ : points.card = n)}

/--
This lemma confirms that the set of possible unit distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem unitDistanceCounts_BddAbove (n : ℕ) : BddAbove <| unitDistanceCounts n := by
  unfold Erdos90.unitDistanceCounts
  unfold Erdos90.unitDistancePairsCount
  use n.choose 2
  rintro _ ⟨points, rfl, rfl⟩
  rw [points.card.choose_two_right]
  gcongr
  refine (card_filter_le _ _).trans_eq ?_
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]


/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)


/--
Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most
$n^{1+O(\frac{1}{\log\log n})}$ many pairs which are distance $1$ apart?
-/
@[category research open, AMS 52]
theorem erdos_90 : answer(sorry) ↔ ∃ (O : ℕ → ℝ) (hO : O =O[atTop] (fun n => 1 / (n : ℝ).log.log)),
    (fun n => (maxUnitDistances n : ℝ)) =ᶠ[atTop] fun (n : ℕ) => (n : ℝ) ^ (1 + O n) := by
  sorry

-- TODO(firsching): add the statements from the rest of the page.

end Erdos90



\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{平面点集单位距离对数量的上界问题}
\author{福莱特.牛墩墩}
\date{\today}

\begin{document}

\maketitle

问题：在 $\mathbb{R}^2$ 中，任意 $n$ 个不同的点所确定的距离为 $1$ 的点对的数量，是否最多为 $n^{1+O(1/\log\log n)}$？

\section*{结论}
答案是否定的。更准确地说，目前并不知道是否每个 $n$ 点集都满足 $n^{1+O(1/\log\log n)}$ 的上界。已知最好的下界和上界表明，单位距离对的数量可以在 $n^{1+c/\log\log n}$ 到 $O(n^{4/3})$ 之间，其中 $c>0$ 为某个常数。

\section*{已知结果}
\begin{itemize}
    \item \textbf{下界：} Erd\H{o}s 在 1946 年构造了一个 $n$ 个点的集合，其中距离为 $1$ 的点对的数量至少为 $n^{1+\frac{c}{\log\log n}}$，其中 $c$ 是一个正常数（例如 $c=\log 2$ 左右）。这表明单位距离对的数量可以超过 $n^{1+\frac{C}{\log\log n}}$，如果 $C < c$ 且 $n$ 足够大。
    \item \textbf{上界：} 目前最好的上界是 $O(n^{4/3})$，由 Spencer、Szemerédi 和 Trotter 等人利用交叉数定理等方法得到。注意 $n^{4/3}$ 比 $n^{1+O(1/\log\log n)}$ 增长得更快，因为对于任意固定的 $C$，当 $n$ 充分大时，$n^{4/3} / n^{1+C/\log\log n} = n^{1/3 - C/\log\log n} \to \infty$。
\end{itemize}

\section*{讨论}
问题中的表达式 $n^{1+O(1/\log\log n)}$ 意味着存在常数 $C$，使得单位距离对的数量不超过 $n^{1+C/\log\log n}$。由于 Erd\H{o}s 的构造给出了指数中的常数为 $c$，若 $C < c$，则该构造将超过所述上界，因此不能断言对所有点集该上界都成立。虽然我们可以取 $C$ 足够大以包含已知构造，但目前并未证明存在这样的 $C$ 使得上界成立。事实上，猜想单位距离对的数量为 $n^{1+o(1)}$，但尚未被证明或否定。

因此，基于当前知识，我们不能说平面中任意 $n$ 点集最多包含 $n^{1+O(1/\log\log n)}$ 个距离为 $1$ 的点对。

\end{document}



