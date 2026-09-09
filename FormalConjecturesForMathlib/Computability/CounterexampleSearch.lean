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
public import Mathlib.Computability.Partrec

/-!
# Partial search for a counterexample bound

`Nat.rfind` gives the least input bound refuting an entire finite prefix of candidates.
Its domain is left partial: totality is equivalent to generic candidate separation.
The enumeration and the Boolean check must be supplied; there is no complexity-class bridge here.

The minimization operation and its contracts are from Mathlib's `Computability.Partrec`.
-/

@[expose] public section

namespace Computability.FiniteTests

variable {α β : Type*} (candidates : Enumeration α) (inputs : Enumeration β)
  (check : α → β → Bool)

/-- The least successful counterexample bound, undefined when no bound suffices. -/
def counterexampleBound (s : ℕ) : Part ℕ :=
  Nat.rfind fun n ↦ Part.some (excludes candidates inputs check s n)

theorem mem_counterexampleBound {s n : ℕ} :
    n ∈ counterexampleBound candidates inputs check s ↔
      Excludes candidates inputs check s n ∧
      ∀ m < n, ¬ Excludes candidates inputs check s m := by
  change (n ∈ Nat.rfind (fun m ↦ Part.some (excludes candidates inputs check s m))) ↔ _
  exact (Nat.mem_rfind (p := fun m ↦ Part.some (excludes candidates inputs check s m))).trans
    (by simp [excludes])

theorem counterexampleBound_spec {s n : ℕ}
    (h : n ∈ counterexampleBound candidates inputs check s) :
    Excludes candidates inputs check s n :=
  ((mem_counterexampleBound candidates inputs check).mp h).1

theorem counterexampleBound_le {s n m : ℕ}
    (h : n ∈ counterexampleBound candidates inputs check s)
    (hm : Excludes candidates inputs check s m) : n ≤ m := by
  by_contra hn
  exact ((mem_counterexampleBound candidates inputs check).mp h).2 m (by omega) hm

@[simp]
theorem counterexampleBound_dom (s : ℕ) :
    (counterexampleBound candidates inputs check s).Dom ↔
      ∃ n, Excludes candidates inputs check s n := by
  exact (Nat.rfind_dom (p := fun n ↦ Part.some (excludes candidates inputs check s n))).trans
    (by simp [excludes])

/-- An explicit computability hypothesis on the finite checker yields partial recursiveness. -/
theorem counterexampleBound_partrec
    (h : Computable₂ (excludes candidates inputs check)) :
    Partrec (counterexampleBound candidates inputs check) :=
  Partrec.rfind h.partrec.to₂

/-- Totality of this search is exactly separation for the supplied candidate and input families. -/
theorem counterexampleBound_total_iff :
    (∀ s, (counterexampleBound candidates inputs check s).Dom) ↔ Separation check := by
  simp only [counterexampleBound_dom]
  exact (separation_iff_excludes candidates inputs check).symm

end Computability.FiniteTests
