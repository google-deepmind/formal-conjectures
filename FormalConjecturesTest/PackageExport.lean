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
# Package export fixtures

Small statements for testing the package-backed workspace exporter. The source
theorems intentionally contain `sorry` so they cannot supply accepted proofs.
-/

namespace PackageExportFixture

universe u

def twice (n : Nat) : Nat := n + n

@[category test, AMS 11]
theorem plain : 2 + 2 = (4 : Nat) := by sorry

@[category test, AMS 11]
theorem localDefinition (n : Nat) : twice n = n + n := by sorry

@[category test, AMS 11]
theorem proposition : answer(sorry) ↔ twice 2 = 4 := by sorry

@[category test, AMS 11]
theorem numerical : twice 2 = (answer(sorry) : Nat) := by sorry

@[category test, AMS 11]
theorem dependent (n : Nat) : (answer(sorry) : Fin (n + 1)).val ≤ n := by sorry

@[category test, AMS 11]
theorem twoAnswers : (answer(sorry) : Nat) + (answer(sorry) : Nat) = 4 := by sorry

@[category test, AMS 1]
theorem polymorphic {α : Type u} (x : α) : x = x := by sorry

private def hidden (n : Nat) : Nat := n + 1

@[category test, AMS 11]
theorem privateDefinition : hidden 0 = 1 := by sorry

@[category test, AMS 03]
theorem implicitUniverse {α : Type*} (x : α) : x = x := by sorry

@[category test, AMS 11]
theorem proofInType : (⟨0, by decide⟩ : Fin 1).val = 0 := by sorry

end PackageExportFixture
