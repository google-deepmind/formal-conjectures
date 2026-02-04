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
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Rify

open Filter

/-- Say a sequence is lacunary if there exists some $\lambda > 1$ such that
$a_{n+1}/a_n > \lambda$ for all sufficiently large $n$. -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

/-- Every lacunary sequence is eventually strictly increasing. -/
lemma IsLacunary.eventually_lt {n : ℕ → ℕ} (hn : IsLacunary n) : ∀ᶠ k in atTop, n k < n (k + 1) := by
  obtain ⟨c, hc, h⟩ := hn
  obtain ⟨N, h⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨N, fun b hb ↦ ?_⟩
  grw [hc] at h
  simpa using h _ hb
