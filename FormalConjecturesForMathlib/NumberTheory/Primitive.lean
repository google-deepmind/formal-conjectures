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


public import Mathlib.Data.Nat.Squarefree

@[expose] public section

/-!
# Primitive elements of a set with respect to divisibility

An element `n` is *primitive* in a set `S ⊆ ℕ` if `n ∈ S` and no proper divisor of `n` is in `S`.

This concept appears naturally when studying sequences closed under "divisor inheritance" -
if every member `n` of a sequence has the property that `m * n` is also in the sequence
for coprime `m`, then the primitive elements generate the entire sequence.

## Main definitions

* `Set.IsPrimitive`: A natural number `n` is primitive in `S` if `n ∈ S` and
  `n.properDivisors` is disjoint from `S`.
* `Set.primitives`: The set of primitive elements of `S`.

## Main results

* `Set.IsPrimitive.mem`: A primitive element is in the set.
* `Set.IsPrimitive.not_mem_of_properDivisor`: Proper divisors of a primitive element are not
  in the set.
* `Set.one_isPrimitive_iff`: `1` is primitive in `S` iff `1 ∈ S`.
* `Set.prime_isPrimitive_iff`: A prime `p` is primitive in `S` iff `p ∈ S` and `1 ∉ S`.
-/

namespace Set

/-- An element `n` is *primitive* in a set `S ⊆ ℕ` if `n ∈ S` and no proper divisor of `n`
is in `S`. -/
def IsPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

/-- The set of primitive elements of `S`. -/
def primitives (S : Set ℕ) : Set ℕ :=
  {n | S.IsPrimitive n}

theorem IsPrimitive.mem {S : Set ℕ} {n : ℕ} (h : S.IsPrimitive n) : n ∈ S := h.1

theorem IsPrimitive.disjoint_properDivisors {S : Set ℕ} {n : ℕ} (h : S.IsPrimitive n) :
    Disjoint (n.properDivisors : Set ℕ) S := h.2

theorem IsPrimitive.not_mem_of_properDivisor {S : Set ℕ} {n d : ℕ} (h : S.IsPrimitive n)
    (hd : d ∈ n.properDivisors) : d ∉ S :=
  Set.disjoint_left.mp h.2 hd

theorem IsPrimitive.not_mem_of_dvd_of_lt {S : Set ℕ} {n d : ℕ} (h : S.IsPrimitive n)
    (hdvd : d ∣ n) (hlt : d < n) : d ∉ S :=
  h.not_mem_of_properDivisor (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩)

theorem isPrimitive_iff {S : Set ℕ} {n : ℕ} :
    S.IsPrimitive n ↔ n ∈ S ∧ ∀ d ∈ n.properDivisors, d ∉ S := by
  simp only [IsPrimitive, Set.disjoint_left, Finset.mem_coe]

theorem isPrimitive_iff' {S : Set ℕ} {n : ℕ} (_hn : 0 < n) :
    S.IsPrimitive n ↔ n ∈ S ∧ ∀ d, d ∣ n → d < n → d ∉ S := by
  rw [isPrimitive_iff]
  constructor <;> intro ⟨hmem, hdiv⟩
  · exact ⟨hmem, fun d hd hlt => hdiv d (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)⟩
  · exact ⟨hmem, fun d hd => hdiv d (Nat.mem_properDivisors.mp hd).1 (Nat.mem_properDivisors.mp hd).2⟩

theorem mem_primitives_iff {S : Set ℕ} {n : ℕ} : n ∈ S.primitives ↔ S.IsPrimitive n := Iff.rfl

@[simp]
theorem primitives_subset {S : Set ℕ} : S.primitives ⊆ S := fun _ h => h.mem

theorem one_isPrimitive_iff {S : Set ℕ} : S.IsPrimitive 1 ↔ 1 ∈ S := by
  simp [isPrimitive_iff, Nat.properDivisors_one]

theorem prime_isPrimitive_iff {S : Set ℕ} {p : ℕ} (hp : p.Prime) :
    S.IsPrimitive p ↔ p ∈ S ∧ 1 ∉ S := by
  simp [isPrimitive_iff, hp.properDivisors]

end Set
