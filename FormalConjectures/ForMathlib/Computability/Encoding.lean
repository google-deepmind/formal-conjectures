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

import Mathlib.Computability.Encoding

open Computability

section encodings
/-!
Encodings taken from Daniel Weber,
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Formalise.20the.20proposition.20P.20.E2.89.A0NP/with/453031558
-/

def finEncodingListBool : Computability.FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := Option.some
  decode_encode _ := rfl
  ΓFin := inferInstance

@[simp]
lemma getLeft?_comp_inl {α β : Type*} :
    Sum.getLeft? ∘ @Sum.inl α β = Option.some := by
  ext
  simp

@[simp]
lemma getLeft?_comp_inr {α β : Type*} :
    Sum.getLeft? ∘ @Sum.inr α β = fun _ ↦ Option.none := by
  ext
  simp

@[simp]
lemma getRight?_comp_inl {α β : Type*} :
    Sum.getRight? ∘ @Sum.inl α β = fun _ ↦ Option.none := by
  ext
  simp

@[simp]
lemma getRight?_comp_inr {α β : Type*} :
    Sum.getRight? ∘ @Sum.inr α β = Option.some := by
  ext
  simp

@[simp]
lemma List.filterMap_none {α β : Type*} (l : List α) :
    l.filterMap (fun _ ↦ @Option.none β) = [] := by
  induction l <;> simp [*]

def pairFinEncoding {α β : Type*} (ea : FinEncoding α) (eb : FinEncoding β) :
    Computability.FinEncoding (α × β) where
  /- The pair encoding language is the direct sum of the individual encoding languages -/
  Γ := ea.Γ ⊕ eb.Γ
  /- The pair encoding function is to concatenate the individual encodings -/
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  /- The decoding function is to filter symbols by the encoding languages they correspond to
  and decode the parts separately. -/
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
                                  (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by
    simp [List.filterMap_append, ea.decode_encode, eb.decode_encode]
  ΓFin := inferInstance

end encodings
