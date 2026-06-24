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
# Erdős Problem 726

*References:*
- [erdosproblems.com/726](https://www.erdosproblems.com/726)
- [EGRS75] Erdős, P., and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., On the prime factors of
  $(\sp{2n}\sb{n})$. Math. Comp. (1975), 83-92.
-/

open Nat Filter Finset
open scoped Topology Asymptotics

namespace Erdos726

/--
As $n\to \infty$ ranges over integers
$\sum_{p\leq n}1_{n\in (p/2,p)\pmod{p}}\frac{1}{p}\sim \frac{\log\log n}{2}$?

A conjecture of Erdős, Graham, Ruzsa, and Straus [EGRS75].

By $n\in (p/2,p)\pmod{p}$ we mean $n\equiv r\pmod{p}$ for some integer $r$ with $p/2<r<p$.
-/
@[category research open, AMS 11]
theorem erdos_726 :
    answer(sorry) ↔
      (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
          (fun p ↦ p.Prime ∧ ((p : ℕ) : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
        (1 : ℝ) / ((p : ℕ) : ℝ))
      ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by
  sorry

/--
The classical estimate of Mertens states that $\sum_{p\leq n}\frac{1}{p}\sim \log\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_726.variants.mertens_estimate :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by
  sorry

end Erdos726
