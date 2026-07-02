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
# Erdős Problem 519

*References:*
- [erdosproblems.com/519](https://www.erdosproblems.com/519)
- [At61b] Atkinson, F. V., *On sums of powers of complex numbers*. Acta Math. Acad.
  Sci. Hungar. (1961), 185-188.
-/

open scoped BigOperators

namespace Erdos519

/-- The $k$th power sum of a finite sequence of complex numbers. -/
noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ i : Fin n, z i ^ k

/--
Let $z_1,\ldots,z_n\in \mathbb{C}$ with $z_1=1$. Must there exist an absolute constant $c>0$ such
that
\[
\max_{1\leq k\leq n}\left\lvert \sum_{i}z_i^k\right\rvert>c?
\]

Atkinson proved that $c=1/6$ suffices.
-/
@[category research solved, AMS 30, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos519.lean"]
theorem erdos_519 : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ),
        z ⟨0, hn⟩ = 1 →
          ∃ k : Fin n, c < ‖powerSum z (k.val + 1)‖ := by
  sorry

end Erdos519
