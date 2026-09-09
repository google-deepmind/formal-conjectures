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
TODO
-/

open CategoryTheory Abelian Limits

universe u v w

namespace NoLoopsConjectures

/-
Let `R`be an artinian ring, `A` an algebra of finite type and `S`a finitely generated simple module over `A` so that Ext^1(S,A) ≠ 0-/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] (S : ModuleCat.{v} A) [Module.Finite A S] [Simple S]

abbrev Ext1NeZ := ¬ Subsingleton (Ext S (.of A A) 1)

variable (A) in
abbrev noLoopStatement := ∀ n:ℕ , ∃ M : ModuleCat.{v} A, Module.Finite A M ∧ projectiveDimension M > n

/--
In this situation the global dimension (defined as the supremum of proectives dimensions of finitely generated modules over `A`) of `A`is infinite.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem noLoop : noLoopStatement A := by
  sorry

abbrev strongNoLoopStatement := projectiveDimension S = ⊤

/--
In this situation the projective dimension of `S`is infinte.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem strongNoLoop : strongNoLoopStatement S := by
  sorry

abbrev veryStrongNoLoopStatement := ∀ i, ∃ n >i,¬ Subsingleton (Ext S (.of A A) n)

/--
In this situation there are an infinte number of integer `i` such that Ext^i(S,A) are vanishing.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem veryStrongNoLoop : veryStrongNoLoopStatement S:= by
  sorry

@[category test, AMS 16 18]
lemma vStrongImplyStrong: (∀ S: ModuleCat A, Module.Finite A S → Simple S → Ext1NeZ S → veryStrongNoLoopStatement S ) → (∀ S: ModuleCat A, Module.Finite A S → Simple S → Ext1NeZ S → strongNoLoopStatement S ) := by
  intro h S fS sS neZS
  apply ENat.WithBot.eq_top_iff_forall_ge.mpr
  intro m
  apply le_sInf
  rintro b hb
  by_contra!
  rcases h S fS sS neZS m with ⟨n,hn⟩
  exact  hn.2 <| HasProjectiveDimensionLT.subsingleton
    (hX := (hb _ this)) _ _ _ (le_of_lt hn.1 ) _

@[category test, AMS 16 18]
lemma StrongImplyNormal: (∀ S: ModuleCat A, Module.Finite A S → Simple S → Ext1NeZ S → strongNoLoopStatement S ) → (∀ S: ModuleCat A, Module.Finite A S → Simple S → Ext1NeZ S → noLoopStatement A) := fun  h S fS sS neZS n => ⟨S,⟨fS,by
  rw [ h S fS sS neZS]
  apply WithBot.LT.coe_lt_coe <| ENat.natCast_lt_top n⟩⟩

end NoLoopsConjectures
