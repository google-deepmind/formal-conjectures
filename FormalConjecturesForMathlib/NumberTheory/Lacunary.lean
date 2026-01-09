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

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Rify

/-- Say a sequence is lacunary if there exists some $\lambda > 1$ such that
$a_{n+1}/a_n > \lambda$ for all $n\geq 1$. -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ k, c * n k < n (k + 1)

/-- Every lacunary sequence is strictly increasing. -/
lemma IsLacunary.strictMono {n : ℕ → ℕ} (hn : IsLacunary n) : StrictMono n := by
  refine strictMono_nat_of_lt_succ fun k => (Nat.cast_lt (α := ℝ)).mp ?_
  obtain ⟨c, hc⟩ := hn
  refine (hc.2 k).trans_le' ?_
  grw [hc.1, one_mul]
