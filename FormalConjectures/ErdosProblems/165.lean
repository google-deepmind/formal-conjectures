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
# Erdős Problem 165

*References:*
- [erdosproblems.com/165](https://www.erdosproblems.com/165)
- [Er61] Erdős, P., *Graph theory and probability. II*. Canad. J. Math. (1961), 346-352.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er90b] Erdős, Paul, *Problems and results on graphs and hypergraphs: similarities and
  differences*. Mathematics of Ramsey theory (1990), 12-28.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [Sh83] Shearer, J. B., *A note on the independence number of triangle-free graphs*. Discrete
  Math. (1983), 83-87.
- [Ki95] Kim, J. H., *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$*. Random
  Structures Algorithms (1995), 173-207.
- [CJMS25] Campos, M. and Jenssen, M. and Michelen, M. and Sahasrabudhe, J., *A new lower bound
  for the Ramsey numbers $R(3,k)$*. arXiv:2505.13371 (2025).
- [HHKP25] Hefty, Z. and Horn, P. and King, D. and Pfender, F., *Improving $R(3,k)$ in just two
  bites*. arXiv:2510.19718 (2025).
-/

@[expose] public section

open Filter

open scoped Asymptotics

namespace Erdos165

local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

/--
Give an asymptotic formula for $R(3,k)$.
-/
@[category research open, AMS 5]
theorem erdos_165 :
    (fun k : ℕ ↦ (R(3, k) : ℝ)) ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Campos, Jenssen, Michelen and Sahasrabudhe [CJMS25] and Hefty, Horn, King and Pfender [HHKP25]
conjecture that $R(3,k) \sim \frac{k^2}{2\log k}$.
-/
@[category research open, AMS 5]
theorem erdos_165.variants.conjecture :
    (fun k : ℕ ↦ (R(3, k) : ℝ)) ~[atTop] (fun k : ℕ ↦ (k : ℝ) ^ 2 / (2 * Real.log k)) := by
  sorry

/--
Shearer [Sh83] proved $R(3,k) \leq (1+o(1))\frac{k^2}{\log k}$.
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (R(3, k) : ℝ) ≤ (1 + ε) * (k : ℝ) ^ 2 / Real.log k := by
  sorry

/--
Hefty, Horn, King and Pfender [HHKP25] proved $R(3,k) \geq (1/2+o(1))\frac{k^2}{\log k}$,
improving earlier bounds of Kim [Ki95] and Campos, Jenssen, Michelen and Sahasrabudhe [CJMS25].
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k ≤ (R(3, k) : ℝ) := by
  sorry

end Erdos165
