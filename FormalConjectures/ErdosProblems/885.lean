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
# Erdős Problem 885

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., The factor-difference set of integers. (1997)
- [Ji99] Jiménez-Urroz, J., A note on a conjecture of Erdős and {R}osenfeld. (1999)
- [Br19] Bremner, A., On a problem of Erdős related to common factor differences. (2019)
-/

open Nat Set Finset

namespace Erdos885

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def FactorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/--
Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that
$|\cap_i D(N_i)| \geq k$?
-/
@[category research open, AMS 11]
theorem erdos_885 : ∀ k ≥ 1,
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, FactorDifferenceSet n).ncard ≥ k := by
  sorry

/--
Erdős and Rosenfeld [ErRo97] proved this is true for $k=2$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, FactorDifferenceSet n).ncard ≥ 2 := by
  sorry

/--
Jiménez-Urroz [Ji99] proved this for $k=3$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, FactorDifferenceSet n).ncard ≥ 3 := by
  sorry

/--
Bremner [Br19] proved this for $k=4$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, FactorDifferenceSet n).ncard ≥ 4 := by
  sorry

end Erdos885
