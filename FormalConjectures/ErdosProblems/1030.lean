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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1030

*References:*
- [erdosproblems.com/1030](https://www.erdosproblems.com/1030)
- [BEFS89] Burr, S. and Erdős, P. and Faudree, R. J. and Schelp, R. H., On the difference between
  consecutive Ramsey numbers. Utilitas Math. (1989), 115-118.
-/

@[expose] public section

open Filter

namespace Erdos1030

/--
Let $R(k,l)$ be the usual Ramsey number: the smallest $n$ such that if the edges of $K_n$ are
coloured red and blue then there exists either a red $K_k$ or a blue $K_l$.

Prove the existence of some $c>0$ such that
$$\lim_{k\to \infty}\frac{R(k+1,k)}{R(k,k)}> 1+c.$$

A problem of Erdős and Sós.
-/
@[category research open, AMS 5]
theorem erdos_1030 :
    ∃ c > (0 : ℝ), ∃ L : ℝ,
      Tendsto (fun k : ℕ ↦
        (SimpleGraph.classicalRamsey (k + 1) k : ℝ) /
          (SimpleGraph.classicalRamsey k k : ℝ)) atTop (nhds L) ∧
      L > 1 + c := by
  sorry

-- TODO: Add variants of the problem.

end Erdos1030
