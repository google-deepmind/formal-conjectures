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

open CategoryTheory Abelian Limits

/-!
TODO
-/

universe u v w

/-
Let `R`be an artinian ring, `A` an algebra of finite type and `S`a finitely generated simple module over `A` so that Ext^1(S,A) ≠ 0-/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] {S : ModuleCat.{v} A} [Module.Finite A S.carrier] [Simple S] (Ext1NeZ : ¬ Subsingleton (Ext S (.of A A) 1))


namespace NoLoopsConjectures
/--
In this situation the global dimension (defined as the supremum of proectives dimensions of finitely generated modules over `A`) of `A`is infinite.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem noLoop : ∀ n, ∃ M: ModuleCat A,∃ _: Module.Finite A M.carrier, projectiveDimension M > n := by
  sorry

/--
In this situation the projective dimension of `S`is infinte.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem strongNoLoop : projectiveDimension S = ⊤ := by
  sorry

/--
In this situation there are an infinte number of integer `i` such that Ext^i(S,A) are vanishing.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem veryStrongNoLoop : ∀ i, ∃ n >i,¬ Subsingleton (Ext S (.of A A) n)  := by
  sorry

end NoLoopsConjectures
