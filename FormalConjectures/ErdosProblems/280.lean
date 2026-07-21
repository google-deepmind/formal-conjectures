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
# Erdős Problem 280

*References:*
- [erdosproblems.com/280](https://www.erdosproblems.com/280)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos280

open Filter

/-- The integer `m` is covered by one of the first `k` chosen congruence classes. -/
def isCoveredBy (n a : ℕ → ℕ) (m k : ℕ) : Prop :=
  ∃ i ∈ Finset.Icc 1 k, m % n i = a i

/-- The number of integers below `n k` not covered by the first `k` congruence classes. -/
noncomputable def uncoveredCount (n a : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n k)).filter (fun m => ¬ isCoveredBy n a m k)).card

/--
Let $n_1<n_2<\cdots $ be an infinite sequence of integers with associated $a_k\pmod{n_k}$, such that for some $\epsilon>0$ we have $n_k>(1+\epsilon)k\log k$ for all $k$. Then
\[
\#\{ m<n_k : m\not\equiv a_i\pmod{n_i} \textrm{ for }1\leq i\leq k\}\neq o(k).
\]

Cambie observed that this is false.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos280.lean"]
theorem erdos_280 : answer(False) ↔
    ∀ (n a : ℕ → ℕ), StrictMono n → (∀ i, 1 ≤ i → a i < n i) →
      (∃ ε : ℝ, 0 < ε ∧
        ∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * (k : ℝ) * Real.log (k : ℝ)) →
      ¬ Tendsto
        (fun k : ℕ => (uncoveredCount n a k : ℝ) / (k : ℝ))
        atTop (nhds 0) := by
  sorry

end Erdos280
