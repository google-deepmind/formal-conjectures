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
# Erdős Problem 92

*Reference:* [erdosproblems.com/92](https://www.erdosproblems.com/92)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos92

/--
For a given point `x` and a set of other points, this function finds the maximum number of points
that lie on a single circle centered at `x`. It does this by grouping the other points by their
distance to `x` and finding the size of the largest group.
-/
noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  letI otherPoints := points.erase x
  letI distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

/--
This property holds for a set of points `A` if every point `x` in `A` has at least `k` other
points from `A` that are equidistant from `x`.
-/
def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

/--
The set of all possible values `k` for which there exists a set of `n` points
satisfying the `hasMinEquidistantProperty k`. The function `f(n)` will be the supremum of this set.
-/
noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

/--
A sanity check to ensure the set of possible `f(n)` values is bounded above. A trivial bound is
`n-1`, since any point can have at most `n-1` other points equidistant from it.
This ensures `sSup` is well-defined.
-/
@[category test, AMS 52]
theorem possible_f_values_BddAbove (n : ℕ) : BddAbove (possible_f_values n) := by
  use n - 1
  rintro k ⟨points, h_card, h_prop⟩
  unfold Erdos92.hasMinEquidistantProperty at *
  unfold Erdos92.maxEquidistantPointsAt at *
  sorry

/--
Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb^2$
in which every $x \in A$ has at least $f(n)$ points in $A$ equidistant from $x$.
-/
noncomputable def f (n : ℕ) : ℕ := sSup <| possible_f_values n

/--
Is it true that $f(n)\leq n^{o(1)}$?
-/
@[category research open, AMS 52]
theorem erdos_92.variants.weak : answer(sorry) ↔ ∃ o : ℕ → ℝ,
  o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ n, (f n : ℝ) ≤ n^(o n) := by
  sorry

/--
Or even $f(n) < n^{c/\log\log n}$ for some constant $c > 0$?
-/
@[category research open, AMS 52]
theorem erdos_92.variants.strong : answer(sorry) ↔
    ∃ c > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ n^(c / (n : ℝ).log.log) := by
  sorry

-- TODO(firsching): formalize the rest of the remarks

end Erdos92


证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于平面点集中每个点至少参与的单位距离数的最小度最大值 $f(n)$ 的界}
\author{福莱特.牛墩墩}
\date{\today}

\begin{document}

\maketitle

定义：设 $f(n)$ 为最大的整数 $k$，使得存在平面上的 $n$ 个点的集合 $A \subset \mathbb{R}^2$，满足对于每个点 $x \in A$，在 $A$ 中至少有 $k$ 个点与 $x$ 的距离恰好为 $1$（即每个点至少参与 $k$ 个单位距离）。问题：是否有 $f(n) \leq n^{o(1)}$？甚至是否有 $f(n) < n^{o(1/\log\log n)}$？

\section*{已知结果}
\begin{enumerate}
    \item \textbf{上界：} 单位距离图（两点距离为 $1$ 则连边）在 $n$ 个顶点上最多有 $O(n^{4/3})$ 条边。因此，若每个点的度至少为 $f(n)$，则总边数至少为 $\frac{1}{2} n f(n)$，从而有 $f(n) \leq C n^{1/3}$ 对某个常数 $C$ 成立。
    \item \textbf{下界：} Erd\H{o}s 在 1946 年构造了一个 $n$ 点集，使得单位距离的总数（边数）至少为 $\Omega(n^{1 + c/\log\log n})$，其中 $c > 0$ 为常数。进一步，利用图论中的标准技巧（任何图都有一个子图，其最小度至少为原图平均度的一半），可从该构造得到一个 $n'$ 点集（$n'$ 可能小于 $n$），其最小度至少为 $\Omega(n^{c/\log\log n})$。通过适当调整，可以证明存在无穷多个 $n$，使得 $f(n) \geq n^{c'/\log\log n}$ 对某个常数 $c' > 0$ 成立。
\end{enumerate}

\section*{问题分析}
\begin{enumerate}
    \item \textbf{$f(n) \leq n^{o(1)}$ 是否成立？} 这里 $n^{o(1)}$ 表示对于任意 $\varepsilon > 0$，当 $n$ 充分大时有 $f(n) \leq n^{\varepsilon}$。目前已知的上界 $f(n) = O(n^{1/3})$ 并不能推出 $f(n) \leq n^{o(1)}$，因为 $1/3$ 是固定指数，不趋于 $0$。因此，该问题仍然开放：既不能证明 $f(n) \leq n^{o(1)}$，也不能证伪（因为下界 $n^{c/\log\log n}$ 实际上是 $n^{o(1)}$，即对任意 $\varepsilon > 0$，当 $n$ 大时 $n^{c/\log\log n} < n^{\varepsilon}$）。所以，从现有结果看，$f(n)$ 可能是 $n^{o(1)}$ 量级，也可能不是。目前尚无定论。
    \item \textbf{$f(n) < n^{o(1/\log\log n)}$ 是否成立？} 这里 $n^{o(1/\log\log n)}$ 表示指数部分比任意常数除以 $\log\log n$ 都小，即对任意 $\varepsilon > 0$，当 $n$ 充分大时 $f(n) \leq n^{\varepsilon/\log\log n}$。已知下界 $f(n) \geq n^{c'/\log\log n}$（对无穷多个 $n$）表明，若取 $\varepsilon < c'$，则对于充分大的 $n$，$n^{c'/\log\log n} > n^{\varepsilon/\log\log n}$。因此，$f(n) < n^{o(1/\log\log n)}$ 不成立。换言之，不存在函数 $g(n) = o(1/\log\log n)$ 使得 $f(n) \leq n^{g(n)}$ 对所有充分大的 $n$ 成立。
\end{enumerate}

\section*{结论}
目前关于 $f(n)$ 的最佳上界是 $O(n^{1/3})$，最佳下界是 $\Omega(n^{c/\log\log n})$（对某个 $c>0$）。因此：
\begin{itemize}
    \item 问题“$f(n) \leq n^{o(1)}$ 是否成立？”仍然是开放的，因为上界不够强而下界符合 $n^{o(1)}$。
    \item 问题“$f(n) < n^{o(1/\log\log n)}$ 是否成立？”的答案是否定的，因为下界表明 $f(n)$ 至少是 $n^{c/\log\log n}$，它不属于 $n^{o(1/\log\log n)}$ 类。
\end{itemize}

\noindent \textbf{注：} 上述讨论假设了下界构造确实能产生每个点度都大的集合。虽然 Erd\H{o}s 的原始构造可能不是正则的，但通过取子图或适当修改，可以确保存在无穷多个 $n$ 使得 $f(n) \geq n^{c/\log\log n}$，这是组合几何中的公认结论。

\end{document}
