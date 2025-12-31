/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 252

*References:*
 - [erdosproblems.com/252](https://www.erdosproblems.com/252)
 - [ErSt71] Erdös, P., and E. G. Straus. "Some number theoretic results." Pacific J. Math 36 (1971):
    635-646.
 - [ErSt74] Erdős, Paul, and Ernst Straus. "On the irrationality of certain series." Pacific journal
    of mathematics 55.1 (1974): 85-92.
 - [ErKa54] P. Erdős, M. Kac, Amer. Math. Monthly 61 (1954), Problem 4518.
 - [ScPu06] Schlage-Puchta, J. C., The irrationality of a number theoretical series. Ramanujan J.
    (2006), 455-460.
 - [FLC07] Friedlander, J. B. and Luca, F. and Stoiciu, M., On the irrationality of a divisor
    function series. Integers (2007).
 - [Pr22] Pratt, K., The irrationality of a divisor function series of Erdős and Kac.
    arXiv:2209.11124 (2022).
-/

open scoped Nat

namespace Erdos252

def σ (k : ℕ) (n : ℕ) : ℕ := ∑ d : {d : Fin (n + 1) // d.1 ∣ n}, d ^ k

/-- `∑ σ 0 n / n!` is irrational. `σ 0 n` is just the number of divisors of `n`, and this is proved
in [ErSt71]. -/
@[category research solved, AMS 11]
theorem erdos_252_0 : Irrational (∑' n : ℕ, σ 0 n / (n ! : ℝ)) := by
  sorry

/-- `∑ σ 1 n / n!` is irrational. This is proved in [ErSt74]. -/
@[category research solved, AMS 11]
theorem erdos_252_1 : Irrational (∑' n : ℕ, σ 1 n / (n ! : ℝ)) := by
  sorry


/-- `∑ σ 2 n / n!` is irrational. This is proved in [ErKa54]. -/
@[category research solved, AMS 11]
theorem erdos_252_2 : Irrational (∑' n : ℕ, σ 2 n / (n ! : ℝ)) := by
  sorry

/-- `∑ σ 3 n / n!` is irrational. This is proved in [ScPu06] and [FLC07]. -/
@[category research solved, AMS 11]
theorem erdos_252_3 : Irrational (∑' n : ℕ, σ 3 n / (n ! : ℝ)) := by
  sorry

/-- `∑ σ 4 n / n!` is irrational. This is proved in [Pr22]. -/
@[category research solved, AMS 11]
theorem erdos_252_4 : Irrational (∑' n : ℕ, σ 4 n / (n ! : ℝ)) := by
  sorry

/--
For a fixed `k ≥ 5`, is `∑ σ k n / n!` irrational?.
-/
@[category research open, AMS 11]
theorem erdos_252_ge_5 {k : ℕ} (hk : k ≥ 5) :
    Irrational (∑' n : ℕ, σ k n / (n ! : ℝ)) ↔ answer(sorry) := by
  sorry

end Erdos252
