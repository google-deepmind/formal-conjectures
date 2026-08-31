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
# Zaremba's conjecture (1972)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Zaremba%27s_conjecture)
* [Za72] Zaremba, S. K. (1972). "La méthode des «bons treillis» pour le calcul des intégrales
  multiples." In *Applications of Number Theory to Numerical Analysis*, Academic Press,
  pp. 39--119.
* [BK14] Bourgain, J. and Kontorovich, A. (2014). "On Zaremba's conjecture." *Ann. of Math.*
  180, pp. 137--196. [arXiv:1107.3776](https://arxiv.org/abs/1107.3776)
* [Hu15] Huang, S. (2015). "An improvement to Zaremba's conjecture." *Geom. Funct. Anal.* 25,
  pp. 860--914. [arXiv:1310.3772](https://arxiv.org/abs/1310.3772)
-/

open Filter

namespace ZarembaConjecture

/-- The **continuant** `K(a₁, …, aₖ)`: the denominator of the finite continued fraction
`[0; a₁, …, aₖ]`, computed by the forward recurrence `q₀ = 1`, `q₋₁ = 0`,
`qᵢ = aᵢ qᵢ₋₁ + qᵢ₋₂`. -/
def continuant (l : List ℕ) : ℕ :=
  (l.foldl (fun p a => (a * p.1 + p.2, p.1)) ((1, 0) : ℕ × ℕ)).1

/-- `m` is a **Zaremba denominator for `A`**: `m` is the continuant of a nonempty word with
partial quotients in `{1, …, A}`. Equivalently, `m` is the denominator of a reduced fraction
`p/m` whose continued-fraction expansion has all partial quotients at most `A`. -/
def IsZarembaDenominator (A m : ℕ) : Prop :=
  ∃ l : List ℕ, l ≠ [] ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ A) ∧ continuant l = m

/--
**Zaremba's conjecture (1972).**

Every positive integer is the denominator of a finite continued fraction all of whose partial
quotients are at most `5`; i.e. every `m ≥ 1` is a continuant of a word over `{1, …, 5}`.
-/
@[category research open, AMS 11]
theorem zaremba_conjecture :
    ∀ m : ℕ, 1 ≤ m → IsZarembaDenominator 5 m := by
  sorry

open Classical in
/--
**Bourgain–Kontorovich (2014): density one for `A = 50`.**

The set of Zaremba denominators for `A = 50` has natural density `1`.

*Reference:* [BK14].
-/
@[category research solved, AMS 11]
theorem zaremba_conjecture.variants.bourgain_kontorovich :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun m => 1 ≤ m ∧ IsZarembaDenominator 50 m).card : ℝ) / N)
      atTop (nhds 1) := by
  sorry

open Classical in
/--
**Huang (2015): density one for `A = 5`.**

The set of Zaremba denominators for `A = 5` itself has natural density `1`.

*Reference:* [Hu15].
-/
@[category research solved, AMS 11]
theorem zaremba_conjecture.variants.huang :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun m => 1 ≤ m ∧ IsZarembaDenominator 5 m).card : ℝ) / N)
      atTop (nhds 1) := by
  sorry

/--
**The conjecture for `m ≤ 10`.**

Explicit witnesses: `1 = K(1)`, `2 = K(2)`, …, `5 = K(5)`, `6 = K(1,5)`, `7 = K(1,2,2)`,
`8 = K(1,1,1,2)`, `9 = K(1,3,2)`, `10 = K(3,3)`.
-/
@[category test, AMS 11]
theorem zaremba_conjecture.variants.le_ten (m : ℕ) (h1 : 1 ≤ m) (h10 : m ≤ 10) :
    IsZarembaDenominator 5 m := by
  interval_cases m
  · exact ⟨[1], by simp, by decide, by decide⟩
  · exact ⟨[2], by simp, by decide, by decide⟩
  · exact ⟨[3], by simp, by decide, by decide⟩
  · exact ⟨[4], by simp, by decide, by decide⟩
  · exact ⟨[5], by simp, by decide, by decide⟩
  · exact ⟨[1, 5], by simp, by decide, by decide⟩
  · exact ⟨[1, 2, 2], by simp, by decide, by decide⟩
  · exact ⟨[1, 1, 1, 2], by simp, by decide, by decide⟩
  · exact ⟨[1, 3, 2], by simp, by decide, by decide⟩
  · exact ⟨[3, 3], by simp, by decide, by decide⟩

end ZarembaConjecture
