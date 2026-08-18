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
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Dyadic channels of Euler's totient

Splitting `n` by its residue modulo a power of two decomposes the totient
sequence into channels `n ↦ φ (2 ^ j * n + r)`. This file names those channels
and the two index types under which their rational span is usually described:
all channels of level at most `e`, and all channels at once.

The level-`0` channel is the totient sequence itself
(`Nat.totientKernelSeq_zero_zero`), so a statement about the span of these
families is a statement about the coefficients of `∑ φ(n) / 2 ^ n`.
-/

open scoped Nat

namespace Nat

/-- The `(j, r)` dyadic channel of Euler's totient: the rational-valued
sequence `n ↦ φ (2 ^ j * n + r)`. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  φ (2 ^ j * n + r)

@[simp]
theorem totientKernelSeq_apply (j r n : ℕ) :
    totientKernelSeq j r n = φ (2 ^ j * n + r) := rfl

/-- The level-`0` channel is the totient sequence itself. -/
theorem totientKernelSeq_zero_zero : totientKernelSeq 0 0 = fun n => (φ n : ℚ) := by
  funext n
  simp

/-- The index of the dyadic totient channels of level at most `e`: a level
`j ≤ e` together with a residue modulo `2 ^ j`. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- Every dyadic totient channel of level at most `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

@[simp]
theorem totientKernelThroughLevelFamily_apply (e : ℕ)
    (j : Fin (e + 1)) (r : Fin (2 ^ j.val)) :
    totientKernelThroughLevelFamily e ⟨j, r⟩ = totientKernelSeq j.val r.val := rfl

/-- The index of all dyadic totient channels: a level `j` together with a
residue modulo `2 ^ j`. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

/-- Every dyadic totient channel. -/
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

@[simp]
theorem fullTotientKernelFamily_apply (j : ℕ) (r : Fin (2 ^ j)) :
    fullTotientKernelFamily ⟨j, r⟩ = totientKernelSeq j r.val := rfl

/-- The index type of the odd-core description of the dyadic totient span: two
exceptional generators together with one generator per dyadic channel. -/
abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

end Nat
