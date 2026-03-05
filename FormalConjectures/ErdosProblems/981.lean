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
# Erdős Problem 981

*Reference:* [erdosproblems.com/981](https://www.erdosproblems.com/981)

For every ε > 0, let f_ε(p) be the smallest m such that ∑_{n≤N} (n/p) < εN for all N ≥ m.
Is it true that ∑_{p<x} f_ε(p) ~ c_ε · x/(log x) for some constant c_ε > 0?
Proved by Elliott [El69].

[El69] Elliott, P. D. T. A., _On the mean value of $f(p)$_. Proc. London Math. Soc. (3) 21
(1970), 28–96.
-/

open Filter

open scoped Topology Real

namespace Erdos981

/-- The partial sum of Legendre symbols $(n/p)$ for $n = 1, \ldots, N$.
    We use the Jacobi symbol which coincides with the Legendre symbol for prime $p$. -/
def legendrePartialSum (p : ℕ) (N : ℕ) : ℤ :=
  (Finset.Icc 1 N).sum (fun n => jacobiSym (n : ℤ) p)

/-- $f_\varepsilon(p)$: the smallest positive integer $m$ such that for all $N \ge m$,
    $\sum_{n \le N} (n/p) < \varepsilon \cdot N$. Returns $0$ if no such $m$ exists. -/
noncomputable def fEpsilon (ε : ℝ) (p : ℕ) : ℕ :=
  sInf {m : ℕ | m ≥ 1 ∧ ∀ N : ℕ, N ≥ m → (legendrePartialSum p N : ℝ) < ε * (N : ℝ)}

/--
Erdős Problem 981 (proved by Elliott [El69]):

For every $\varepsilon > 0$, there exists $c_\varepsilon > 0$ such that
$$\sum_{\substack{p < x \\ p \text{ prime}}} f_\varepsilon(p) \sim c_\varepsilon \cdot
\frac{x}{\log x}.$$

Formulated as: the ratio $\sum_{p < x} f_\varepsilon(p) / (x / \log x)$ tends to
$c_\varepsilon$.
-/
@[category research solved, AMS 11]
theorem erdos_981 (ε : ℝ) (hε : ε > 0) :
    ∃ c : ℝ, c > 0 ∧
      Tendsto
        (fun x : ℕ =>
          (((Finset.range x).filter Nat.Prime).sum (fun p => fEpsilon ε p) : ℝ) /
            ((x : ℝ) / Real.log (x : ℝ)))
        atTop (nhds c) := by
  sorry

end Erdos981
