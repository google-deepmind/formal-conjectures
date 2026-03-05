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
# Erdős Problem 1149

*Reference:* [erdosproblems.com/1149](https://www.erdosproblems.com/1149)

[Va99] Vardi, I., *Computational Recreations in Mathematica* (1999), Problem 1.34.

[BeRi17] Bergelson, V. and Richter, F. K., *Dynamical generalizations of the prime
number theorem and disjointness of additive and multiplicative semigroup actions* (2017).
-/

open Finset Filter Real Classical

open scoped Topology

namespace Erdos1149

/--
Erdős Problem 1149 [Va99, 1.34]:

Let $\alpha > 0$ be a real number, not an integer. The natural density of integers
$n \geq 1$ for which $\gcd(n, \lfloor n^\alpha \rfloor) = 1$ equals $6/\pi^2$.

The constant $6/\pi^2 = 1/\zeta(2)$ is the "probability" that two random integers
are coprime, so this says $n$ and $\lfloor n^\alpha \rfloor$ behave like independent
random integers with respect to coprimality when $\alpha$ is not an integer.

This was proved by Bergelson and Richter [BeRi17].
-/
@[category research solved, AMS 11]
theorem erdos_1149 (α : ℝ) (hα_pos : 0 < α) (hα_not_int : ∀ k : ℤ, (k : ℝ) ≠ α) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        Nat.Coprime n (⌊(n : ℝ) ^ α⌋₊))).card : ℝ) / (x : ℝ))
      atTop (nhds (6 / Real.pi ^ 2)) := by
  sorry

end Erdos1149
