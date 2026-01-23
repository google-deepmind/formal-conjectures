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
# Birch–Tate conjecture

The Birch–Tate conjecture relates the order of K₂ (the tame kernel) of a totally real number field
to the value of the Dedekind zeta function at -1.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Birch%E2%80%93Tate_conjecture)
- J. T. Tate, *Symbols in Arithmetic*, Actes, Congrès Intern. Math., Nice, 1970, Tome 1, Gauthier-Villars (1971), 201–211
-/

namespace BirchTate

variable (F : Type*) [Field F] [NumberField F]

/-! ## Definitions -/

/-- K₂ is the center of the Steinberg group of the ring of integers of a number field F.
Also known as the tame kernel of F. -/
noncomputable def K2 (F : Type*) [Field F] [NumberField F] : Type* := sorry

/-- The order (cardinality) of K₂. -/
noncomputable def K2Order (F : Type*) [Field F] [NumberField F] : ℕ := sorry

/-- The Dedekind zeta function of a number field F evaluated at -1. -/
noncomputable def dedekindZetaAtNegOne (F : Type*) [Field F] [NumberField F] : ℝ := sorry

/-- A number field F is totally real if all its embeddings into ℂ are real. -/
def IsTotallyReal (F : Type*) [Field F] [NumberField F] : Prop := sorry

/-- For a totally real number field F, N is the largest natural number such that
the extension F(ζ_N) has an elementary abelian 2-group as its Galois group. -/
noncomputable def N (F : Type*) [Field F] [NumberField F] (h : IsTotallyReal F) : ℕ := sorry

/-! ## Statement -/

/--
The Birch–Tate conjecture: For a totally real number field F,
let N be the largest natural number such that F(ζ_N) has an elementary abelian 2-group
as its Galois group. Then #K₂ = |N · ζ_F(-1)|.
-/
@[category research open, AMS 19]
theorem birch_tate_conjecture (h : IsTotallyReal F) :
    K2Order F = Int.natAbs ⌊(N F h : ℝ) * dedekindZetaAtNegOne F⌋ := by
  sorry

end BirchTate
