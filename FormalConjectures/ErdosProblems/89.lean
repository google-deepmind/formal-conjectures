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
# Erdős Problem 89

*Reference:* [erdosproblems.com/89](https://www.erdosproblems.com/89)
-/

open Filter
open EuclideanGeometry

namespace Erdos89

/--
The minimum number of distinct distances guaranteed for any set of $n$ points.
-/
noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {(distinctDistances points : ℝ) | (points : Finset ℝ²) (_ : points.card = n)}

/--
Does every set of $n$ distinct points in $\mathbb{R}^2$ determine $\gg \frac{n}{\sqrt{\log n}}$
many distinct distances?
-/
@[category research open, AMS 52]
theorem erdos_89 :
    (fun (n : ℕ) => n/(n : ℝ).log.sqrt) =O[atTop] (fun n => (minimalDistinctDistances n : ℝ)) := by
  sorry

/--
Guth and Katz [GuKa15] proved that there are always $\gg \frac{n}{\log n}$ many distinct distances.

[GuKa15] Guth, Larry and Katz, Nets Hawk, On the Erdős distinct distances problem in the plane. Ann. of Math. (2) (2015), 155-190.
-/
@[category research solved, AMS 52]
theorem erdos_89.variants.n_dvd_log_n :
    (fun (n : ℕ) => n/(n : ℝ).log) =O[atTop] (fun n => (minimalDistinctDistances n : ℝ)) := by
  sorry

/--
This theorem provides a sanity check, showing that the main conjecture (`erdos_89`) is strictly
stronger than the solved Guth and Katz result. It proves that, trivially, if the lower bound
$\frac{n}{\sqrt{\log n}}$ holds, then the weaker lower bound $\frac{n}{\log n}$ must also hold.
-/
@[category test, AMS 52]
theorem erdos_89.variants.implies_n_dvd_log_n (h : type_of% erdos_89) :
    type_of% erdos_89.variants.n_dvd_log_n := by
  refine .trans ?_ h
  have := (Asymptotics.isLittleO_one_left_iff ℝ).mpr <| tendsto_norm_atTop_atTop.comp <|
    (tendsto_rpow_atTop (show 0 < 1/2 by norm_num)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  convert (Asymptotics.isBigO_refl (fun n : ℕ ↦ n/(n : ℝ).log) _).mul this.isBigO using 1
  · simp
  · simp_rw [Function.comp, div_mul, ← Real.sqrt_eq_rpow, Real.div_sqrt]


-- TODO(firsching): formalize the rest of the remarks

end Erdos89

证明过程如下：

\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于平面点集不同距离数量的下界}
\author{福莱特.牛墩墩}
\date{\today}

\begin{document}

\maketitle

问题：在 $\mathbb{R}^2$ 中，是否任意 $n$ 个不同的点所确定的不同的两两距离的数量至少为 $\gg n/\sqrt{\log n}$？即是否存在常数 $c>0$，使得任意 $n$ 点集至少产生 $c n/\sqrt{\log n}$ 个不同的距离？

\section*{结论}
答案是否定的。Erd\H{o}s 在 1946 年构造了一个 $n$ 个点的集合，其中不同距离的数量仅为 $O(n/\sqrt{\log n})$，这表明下界 $\Omega(n/\sqrt{\log n})$ 不成立。

\section*{构造与上界}
考虑一个 $\sqrt{n} \times \sqrt{n}$ 的整数网格点集
\[
G = \{ (i,j) : 1 \le i,j \le \sqrt{n} \},
\]
其中 $n$ 是完全平方数。任意两点间的距离平方为 $(i-i')^2+(j-j')^2$，是两个整数平方和。不同距离的数量不超过不超过 $2n$ 的整数能表示为两个平方数之和的方式数。通过数论分析，Erd\H{o}s 证明了不同距离的数量不超过
\[
\frac{C n}{\sqrt{\log n}}
\]
对于某个常数 $C$。因此，存在点集使得不同距离的数量仅为 $O(n/\sqrt{\log n})$。

\section*{下界进展}
尽管 Erd\H{o}s 猜想不同距离的数量至少为 $n^{1-o(1)}$，但长期以来最好的下界仅为 $n^{c}$ 的形式。目前最好的结果由 Guth 和 Katz 在 2015 年给出，他们证明了至少为 $\Omega(n/\log n)$，随后进一步改进到 $\Omega(n^{0.864})$ 左右。但无论如何，无法达到 $\Omega(n/\sqrt{\log n})$，因为网格例子表明该阶是可能达到的上界。

\section*{总结}
因此，并非每一组 $n$ 个不同的点都决定了至少 $c n/\sqrt{\log n}$ 个不同的距离。相反，存在点集只产生 $O(n/\sqrt{\log n})$ 个不同距离。

\end{document}


