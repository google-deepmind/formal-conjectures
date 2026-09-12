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

import FormalConjecturesUtil

/-!
# Erdős Problem 896

*References:*
- [erdosproblems.com/896](https://www.erdosproblems.com/896)
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval*. Ann. of
  Math. (2) (2008), 367-433.
-/

open Filter

namespace Erdos896

/--
$F(A,B)$ counts the number of $m$ such that $m=ab$ has exactly one solution with $a\in A$ and
$b\in B$.
-/
def F (A B : Finset ℕ) : ℕ :=
  ((A.product B).image (fun p => p.1 * p.2)).filter (fun m =>
    ((A.product B).filter (fun p => p.1 * p.2 = m)).card = 1) |>.card

/--
The maximum of $F(A,B)$ as $A,B$ range over all subsets of $\{1,\ldots,N\}$.
-/
def maxF (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.product (Finset.Icc 1 N).powerset).sup (fun p => F p.1 p.2)

/-- Ford's constant $\delta=1-\frac{1+\log\log 2}{\log 2}\approx 0.086$. -/
noncomputable def fordDelta : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

@[category test, AMS 11]
theorem F_singleton : F {2} {3} = 1 := by decide

@[category test, AMS 11]
theorem F_two_representations : F {1, 2} {1, 2} = 2 := by decide

/--
Estimate the maximum of $F(A,B)$ as $A,B$ range over all subsets of $\{1,\ldots,N\}$, where
$F(A,B)$ counts the number of $m$ such that $m=ab$ has exactly one solution (with $a\in A$ and
$b\in B$).

The order of magnitude of $F(A,B)$ is now known:
$$F(A,B)\asymp \frac{N^2}{(\log N)^\delta(\log\log N)^{3/2}}$$
where $\delta=1-\frac{1+\log\log 2}{\log 2}\approx 0.086$. The upper bound is an immediate
consequence of the bound on the size of $\{1,\ldots,N\}\cdot\{1,\ldots,N\}$ given by Ford [Fo08].
The lower bound was proved by GPT-5.5 Pro (prompted by Chojecki), using a similar result from
[Fo08]; the proof is sketched in the comments.
-/
@[category research solved, AMS 11]
theorem erdos_896 : Asymptotics.IsTheta atTop
    (fun N : ℕ => (maxF N : ℝ))
    (fun N : ℕ => (N : ℝ)^2 /
      ((Real.log N) ^ fordDelta * (Real.log (Real.log N)) ^ ((3:ℝ)/2))) := by
  sorry

end Erdos896
