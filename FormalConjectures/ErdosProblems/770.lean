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
# Erdős Problem 770

*Reference:*
 - [erdosproblems.com/770](https://www.erdosproblems.com/770)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

open Real Set

namespace Erdos770

/-- Let `h n` be the minimal number such that `2 ^ n - 1, ..., (h n) ^ n - 1` are mutually
coprime. -/
noncomputable def h (n : ℕ) : ℕ := sInf
  {a : ℕ∞ | ∃ (m : ℕ), a = m ∧ 1 < m ∧ ∀ i ∈ Finset.Icc 2 m,
  ∀ j ∈ Finset.Icc 2 m, i ≠ j → (i ^ n - 1).Coprime (j ^ n - 1)}

@[category test, AMS 11]
theorem Odd.h_unbounded {n : ℕ} (hn : Odd n)

/--  -/
@[category research open, AMS 11]
theorem erdos_770.log3 : answer(sorry) ↔
    ∃ (C : ℝ), 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n →
    (fun k => (eLpNorm (fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (log (log (log k))) ^ C)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ .range N, f (n k • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry

/-- The following theorem is proved in [Ma66]. -/
@[category research solved, AMS 11]

end Erdos770
