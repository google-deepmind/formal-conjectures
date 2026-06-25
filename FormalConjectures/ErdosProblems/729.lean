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
# Erdős Problem 729

*Reference:* [erdosproblems.com/729](https://www.erdosproblems.com/729)
-/

namespace Erdos729

/--
For any $C > 0$, there exists a constant $K \geq 3$ such that there are infinitely many triples
$(a, b, n)$ with $a + b > n + C \log n$ and the denominator of $n!/(a!\, b!)$ being $K$-smooth (no
prime factor exceeding $K$). This answers the Erdős–Graham–Ruzsa–Straus problem affirmatively.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos729.lean"]
theorem erdos_729 (C : ℝ) (hC : C > 0) :
    ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
      let (a, b, n) := T
      a > 0 ∧ b > 0 ∧ n > 0 ∧
      (a : ℝ) + b > n + C * Real.log n ∧
      ∀ p, p.Prime → p > K →
        padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
  sorry

end Erdos729
