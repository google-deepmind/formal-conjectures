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
(1993) for $n > 2014$. The current smallest known counterexample dimension is $n = 64$, due to
Brouwer and Jenrich (2014).
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
