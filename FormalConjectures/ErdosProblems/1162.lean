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
# Erdős Problem 1162

*References:*
- [erdosproblems.com/1162](https://www.erdosproblems.com/1162)
- [Py93] Pyber, László, *Asymptotic results for permutation groups*. (1993), 197--219.
- [RoTr25] C. Roney-Dougal and G. Tracey, *Subgroups of symmetric groups: enumeration and
  asymptotic properties*. arXiv:2503.05416 (2025).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

open Filter Asymptotics

namespace Erdos1162

/--
$f(n)$ counts the number of subgroups of $S_n$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/--
Give an asymptotic formula for the number of subgroups of $S_n$.
-/
@[category research open, AMS 20]
theorem erdos_1162.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Is there a statistical theorem on their order?
-/
@[category research open, AMS 20]
theorem erdos_1162.parts.ii :
    answer(sorry) ↔
      ∃ μ : ℕ → ℝ, ∀ ε > (0 : ℝ),
        Tendsto (fun n : ℕ ↦
          (Nat.card {H : Subgroup (Equiv.Perm (Fin n)) |
              |Real.log (Nat.card H : ℝ) - μ n| ≤ ε * |μ n|} : ℝ) / f n)
          atTop (nhds 1) := by
  sorry

/--
Let $f(n)$ count the number of subgroups of $S_n$. Pyber [Py93] proved that
$$\log f(n) \asymp n^2.$$
-/
@[category research solved, AMS 20]
theorem erdos_1162.variants.pyber :
    (fun n : ℕ ↦ Real.log (f n : ℝ)) =Θ[atTop] fun n ↦ (n : ℝ) ^ 2 := by
  sorry

/--
Roney-Dougal and Tracey [RoTr25] have proved that
$$\log f(n)=\left(\frac{1}{16}+o(1)\right)n^2.$$

The constant $1/16$ is for logarithms base $2$, equivalently $f(n)=2^{n^2/16+o(n^2)}$.
-/
@[category research solved, AMS 20]
theorem erdos_1162.variants.roney_dougal_tracey :
    Tendsto (fun n : ℕ ↦ Real.logb 2 (f n : ℝ) / (n : ℝ) ^ 2) atTop (nhds (1 / 16 : ℝ)) := by
  sorry

end Erdos1162
