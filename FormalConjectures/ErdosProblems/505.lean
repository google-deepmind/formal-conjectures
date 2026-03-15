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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 505

*Reference:* [erdosproblems.com/505](https://www.erdosproblems.com/505)

Borsuk's conjecture. Originally conjectured by Borsuk in 1933. Disproved by Kahn and Kalai
[KaKa93] for $n > 2014$. The current smallest known counterexample dimension is $n = 64$, due to
Brouwer and Jenrich [BrJe14]. Eggleston [Eg55] proved the conjecture for $n = 3$. Schramm [Sc88]
proved the upper bound $\alpha(n) \leq ((3/2)^{1/2} + o(1))^n$ on the minimum number of pieces
needed. Erdős [Er81b, p.28] suspected the conjecture was false for sufficiently high dimensions.

[Er46b] Erdős, P., _On sets of distances of $n$ points_. Amer. Math. Monthly (1946), 248-250.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981), 27-35.

[Eg55] Eggleston, H. G., _Covering a three-dimensional set with sets of smaller diameter_.
J. London Math. Soc. (1955), 11-24.

[KaKa93] Kahn, J., Kalai, G., _A counterexample to Borsuk's conjecture_. Bull. Amer. Math. Soc.
(N.S.) (1993), 60-62.

[BrJe14] Brouwer, A. E., Jenrich, T., _A 64-dimensional counterexample to Borsuk's conjecture_.
Electron. J. Combin. (2014), Paper 4.29, 3.

[Sc88] Schramm, O., _Illuminating sets of constant width_. Mathematika (1988), 180-189.
-/

open Metric Set

namespace Erdos505

/--
Borsuk's conjecture:
Is every set of diameter $1$ in $\mathbb{R}^n$ the union of at most $n+1$ sets of diameter
$< 1$?

This is trivially true for $n=1$ and easy for $n=2$. Eggleston proved it for $n=3$. In 1981,
Erdős wrote that he suspected it was false for sufficiently high dimensions. Indeed, Kahn and
Kalai disproved it for $n > 2014$. The current smallest known counterexample dimension is
$n = 64$, due to Brouwer and Jenrich.
-/
@[category research solved, AMS 52]
theorem erdos_505 : answer(False) ↔
    ∀ n : ℕ, ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      Metric.diam S = 1 →
      ∃ F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin n)),
        S = ⋃ i, F i ∧ ∀ i, Metric.diam (F i) < 1 := by
  sorry

end Erdos505
