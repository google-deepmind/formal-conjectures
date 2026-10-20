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

public import FormalConjecturesUtil

/-!
# Erdős Problem 709

*References:*
- [erdosproblems.com/709](https://www.erdosproblems.com/709)
- [ErSu59] P. Erdős and J. Surányi, Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs, Mat. Lapok 10 (1959), 39–48.
- [Er92c] P. Erdős, Some of my forgotten problems in number theory, Hardy–Ramanujan J. 15
  (1992), 34–50.
- [vD26] W. van Doorn, On the length of an interval that contains distinct multiples of the
  first $n$ positive integers, Integers (2026), #A7.
-/

@[expose] public section

namespace Erdos709

/-- The block of `length` consecutive positive integers immediately after `start`. -/
def window (start length : ℕ) : Finset ℕ := Finset.Icc (start + 1) (start + length)

/-- A block contains distinct multiples of all elements of `A`. -/
def HasDistinctMultiples (A : Finset ℕ) (start length : ℕ) : Prop :=
  ∃ choice : ℕ → ℕ,
    Set.InjOn choice (A : Set ℕ) ∧
    ∀ a ∈ A, choice a ∈ window start length ∧ a ∣ choice a

/-- The multiplier `k` works for all `n`-element inputs and all starting points.
`M` is required to be the largest element of `A`. -/
def Works (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ),
    A.card = n → M ∈ A → (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) →
    ∀ start : ℕ, HasDistinctMultiples A start (k * M)

/-- `k` is the least multiplier that works for inputs of size `n`. -/
def IsOptimal (n k : ℕ) : Prop := Works n k ∧ ∀ j < k, ¬ Works n j

/-- A matching in a shorter block remains a matching in any longer block. -/
@[category API, AMS 5 11]
theorem matching_mono_length
    (A : Finset ℕ) (start small large : ℕ) (hsmall : small ≤ large)
    (h : HasDistinctMultiples A start small) : HasDistinctMultiples A start large := by
  obtain ⟨choice, hinj, hchoice⟩ := h
  refine ⟨choice, hinj, ?_⟩
  intro a ha
  obtain ⟨hmem, hdvd⟩ := hchoice a ha
  refine ⟨?_, hdvd⟩
  simp only [window, Finset.mem_Icc] at hmem ⊢
  constructor
  · exact hmem.1
  · omega

/-- If multiplier `k` works, every larger multiplier also works. -/
@[category API, AMS 5 11]
theorem works_mono (n k l : ℕ) (hkl : k ≤ l) (h : Works n k) : Works n l := by
  intro A M hcard hmax hbound htwo start
  exact matching_mono_length A start (k * M) (l * M) (Nat.mul_le_mul_right M hkl)
    (h A M hcard hmax hbound htwo start)

/-- Every interval of `M` consecutive positive integers contains a multiple of `a` when
`0 < a ≤ M`. -/
@[category API, AMS 5 11]
theorem exists_multiple_in_window
    (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    ∃ b ∈ window start M, a ∣ b := by
  let r := start % a
  let b := start + (a - r)
  have hr : r < a := Nat.mod_lt start ha
  have heq : start % a + a * (start / a) = start := by
    simpa [Nat.mul_comm] using Nat.mod_add_div start a
  have hbdiv : b = a * (start / a + 1) := by
    have haux : b = a * (start / a) + a := by
      dsimp [b, r]
      omega
    calc
      b = a * (start / a) + a := haux
      _ = a * (start / a + 1) := by ring
  refine ⟨b, ?_, ?_⟩
  · simp only [window, Finset.mem_Icc]
    constructor
    · dsimp [b]
      omega
    · dsimp [b]
      omega
  · exact ⟨start / a + 1, hbdiv⟩

/-- Erdős Problem 709 holds for a singleton input: the multiplier `1` suffices. -/
@[category textbook, AMS 5 11]
theorem erdos_709.variants.singleton : Works 1 1 := by
  intro A M hcard hM hbound htwo start
  have hA : A = {M} := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hMz : M = z := Finset.mem_singleton.mp (hz ▸ hM)
    simpa [hMz] using hz
  obtain ⟨b, hb, hd⟩ :=
    exists_multiple_in_window M M start (by have := htwo M hM; omega) le_rfl
  refine ⟨fun _ => b, ?_, ?_⟩
  · intro u hu v hv _
    rw [hA] at hu hv
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
    exact hu.trans hv.symm
  · intro a ha
    rw [hA] at ha
    have hEq : a = M := Finset.mem_singleton.mp ha
    subst a
    simpa using And.intro hb hd

/-- For singleton inputs, every multiplier at least `1` works. -/
@[category API, AMS 5 11]
theorem works_one_of_one_le (k : ℕ) (hk : 1 ≤ k) : Works 1 k :=
  works_mono 1 1 k hk erdos_709.variants.singleton

end Erdos709
