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
module


public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Rify

@[expose] public section

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

/-- The real-valued analogue of `IsLacunary`. -/
def IsLacunaryReal (a : ℕ → ℝ) : Prop :=
  ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * a k < a (k + 1)

/-- An ℕ-valued sequence is lacunary iff its real cast is lacunary as a real sequence. -/
lemma isLacunary_iff_isLacunaryReal {n : ℕ → ℕ} :
    IsLacunary n ↔ IsLacunaryReal (fun k => (n k : ℝ)) := Iff.rfl

/-- A positive lacunary real-valued sequence is eventually strictly increasing. -/
lemma IsLacunaryReal.eventually_lt {a : ℕ → ℝ} (ha : IsLacunaryReal a)
    (hpos : ∀ᶠ k in atTop, 0 < a k) : ∀ᶠ k in atTop, a k < a (k + 1) := by
  obtain ⟨c, hc, hlac⟩ := ha
  filter_upwards [hlac, hpos] with k hk hp using by nlinarith
