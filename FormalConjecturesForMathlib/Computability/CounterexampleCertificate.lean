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
module

public import FormalConjecturesForMathlib.Computability.FiniteTests
public import Mathlib.Data.Finset.Dedup

/-!
# Finite counterexample certificates

A certificate lists exactly one failing input for each candidate in the specified exhaustive
prefix. Validation checks exact candidate coverage, duplicate keys, input sizes, and failures.
The candidate enumeration determines the scope; a restricted family stays restricted.
-/

@[expose] public section

namespace Computability.FiniteTests

variable {α β : Type*} [DecidableEq α]

/-- Exact coverage with distinct keys and bounded failing inputs. -/
def ValidCertificate (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) (entries : List (α × β)) : Prop :=
  (entries.map Prod.fst).Nodup ∧
    (entries.map Prod.fst).toFinset = candidates.upTo s ∧
    ∀ entry ∈ entries, inputs.size entry.2 ≤ n ∧ check entry.1 entry.2 = false

instance (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) (entries : List (α × β)) :
    Decidable (ValidCertificate candidates inputs check s n entries) := by
  unfold ValidCertificate
  infer_instance

/-- Executable validation against a supplied exhaustive candidate family. -/
def validateCertificate (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) (entries : List (α × β)) : Bool :=
  decide (ValidCertificate candidates inputs check s n entries)

@[simp]
theorem validateCertificate_eq_true (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) (entries : List (α × β)) :
    validateCertificate candidates inputs check s n entries = true ↔
      ValidCertificate candidates inputs check s n entries := by
  simp [validateCertificate]

theorem ValidCertificate.excludes {candidates : Enumeration α} {inputs : Enumeration β}
    {check : α → β → Bool} {s n : ℕ} {entries : List (α × β)}
    (h : ValidCertificate candidates inputs check s n entries) :
    Excludes candidates inputs check s n := by
  intro a ha
  rw [← h.2.1, List.mem_toFinset, List.mem_map] at ha
  obtain ⟨⟨a', x⟩, hx, heq⟩ := ha
  obtain rfl : a' = a := heq
  exact ⟨x, inputs.mem_upTo.mpr (h.2.2 _ hx).1, (h.2.2 _ hx).2⟩

end Computability.FiniteTests
