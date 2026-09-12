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

public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-!
# Polynomial-time search with promises

A solver returns an encoded witness. Its correctness is required on the promised
domain, while its deterministic TM2 running-time bound holds on every encoded input.
A Boolean output specializes this to promise decision. No promise-checking algorithm
or reference implementation is assumed.

For concrete search and promise problems, see Menezes, van Oorschot, and Vanstone,
*Handbook of Applied Cryptography* (1996), Chapter 3, Definitions 3.28, 3.31, and 3.51:
https://cacr.uwaterloo.ca/hac/about/chap3.pdf.
-/

@[expose] public section

namespace ComplexityTheory

variable {α β : Type} [BitstringEncoding α] [BitstringEncoding β]

/-- A total polynomial-time function returning a correct witness on the promised domain. -/
def HasPolyTimeSolver (promise : α → Prop) (relation : α → β → Prop) : Prop :=
  ∃ f : α → β, IsPolyTime f ∧ ∀ x, promise x → relation x (f x)

theorem hasPolyTimeSolver_congr {p q : α → Prop} {r s : α → β → Prop}
    (hp : ∀ x, p x ↔ q x) (hr : ∀ x y, p x → (r x y ↔ s x y)) :
    HasPolyTimeSolver p r ↔ HasPolyTimeSolver q s := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun x hx ↦ (hr x (f x) ((hp x).mpr hx)).mp (h x ((hp x).mpr hx))⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun x hx ↦ (hr x (f x) hx).mpr (h x ((hp x).mp hx))⟩

/-- Restricting the promised domain and weakening the output requirements preserves solvability. -/
theorem HasPolyTimeSolver.mono {p q : α → Prop} {r s : α → β → Prop}
    (h : HasPolyTimeSolver p r) (hp : ∀ x, q x → p x)
    (hr : ∀ x y, q x → r x y → s x y) : HasPolyTimeSolver q s := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, fun x hx ↦ hr x (f x) hx (h x (hp x hx))⟩

/-- An actual polynomial-time function solves its own graph relation. -/
theorem IsPolyTime.hasPolyTimeSolver {f : α → β} (h : IsPolyTime f) (p : α → Prop) :
    HasPolyTimeSolver p (fun x y ↦ y = f x) :=
  ⟨f, h, fun _ _ ↦ rfl⟩

/-- A Boolean solver must answer correctly on the promise, with no constraint elsewhere. -/
def HasPolyTimePromiseDecider (promise predicate : α → Prop) : Prop :=
  HasPolyTimeSolver promise (fun x b ↦ b = true ↔ predicate x)

theorem hasPolyTimePromiseDecider_true (p : α → Prop) :
    HasPolyTimePromiseDecider (fun _ ↦ True) p ↔ HasPolyTimeDecider p := by
  simp [HasPolyTimePromiseDecider, HasPolyTimeSolver, HasPolyTimeDecider]

end ComplexityTheory
