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

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

@[expose] public section

/-! # Difference bases

A *difference basis* for a finite set $S$ is a finite set $A$ such that every element of $S$
can be written as a difference $a - b$ of two elements $a, b \in A$; equivalently $S \subseteq A - A$.
The multiplicative version is a *ratio basis* ($S \subseteq A / A$).

The classical case $S = \{0, 1, \ldots, N\}$ over $\mathbb{Z}$ (or $\mathbb{N}$) recovers the notion
of a *restricted difference basis*, dual to the recreational notion of a *sparse ruler*: a
difference basis for $\{0, \ldots, N\}$ of minimal size is an optimal ruler of length $N$.

## Main definitions

* `Finset.IsRatioBasis A S` (additive: `Finset.IsDifferenceBasis A S`): $S \subseteq A / A$.

## Main results

* `Finset.isRatioBasis_iff`: the elementwise characterization.
* `Finset.IsRatioBasis.mono_left` / `Finset.IsRatioBasis.mono_right`: monotonicity.
* `Finset.IsRatioBasis.card_le_sq`: a ratio basis for $S$ has at least $\sqrt{|S|}$ elements,
  i.e. $|S| \le |A|^2$.

## References

- [Wi63] Wichmann, B. "A note on restricted difference bases." Journal of the London
  Mathematical Society 38 (1963): 465-466.
-/

open scoped Pointwise

namespace Finset
variable {G : Type*} [DecidableEq G] [Div G] {A B S T : Finset G}

/-- A finset $A$ is a *ratio basis* for $S$ if every element of $S$ is a ratio $a / b$ of two
elements $a, b \in A$, i.e. $S \subseteq A / A$. -/
@[to_additive IsDifferenceBasis
/-- A finset $A$ is a *difference basis* for $S$ if every element of $S$ is a difference $a - b$
of two elements $a, b \in A$, i.e. $S \subseteq A - A$. -/]
def IsRatioBasis (A S : Finset G) : Prop := S ⊆ A / A

/-- A finset $A$ is a ratio basis for $S$ iff every $x \in S$ is a ratio of two elements of $A$. -/
@[to_additive isDifferenceBasis_iff
/-- A finset $A$ is a difference basis for $S$ iff every $x \in S$ is a difference of two elements
of $A$. -/]
theorem isRatioBasis_iff : IsRatioBasis A S ↔ ∀ x ∈ S, ∃ a ∈ A, ∃ b ∈ A, a / b = x := by
  simp only [IsRatioBasis, subset_iff, mem_div]

/-- Shrinking the target set preserves being a ratio basis. -/
@[to_additive /-- Shrinking the target set preserves being a difference basis. -/]
theorem IsRatioBasis.mono_left (h : IsRatioBasis A S) (hTS : T ⊆ S) : IsRatioBasis A T :=
  hTS.trans h

/-- Enlarging the basis preserves being a ratio basis. -/
@[to_additive /-- Enlarging the basis preserves being a difference basis. -/]
theorem IsRatioBasis.mono_right (h : IsRatioBasis A S) (hAB : A ⊆ B) : IsRatioBasis B S :=
  h.trans (div_subset_div hAB hAB)

/-- A ratio basis for $S$ has at least $\sqrt{|S|}$ elements: $|S| \le |A|^2$. -/
@[to_additive /-- A difference basis for $S$ has at least $\sqrt{|S|}$ elements: $|S| \le |A|^2$. -/]
theorem IsRatioBasis.card_le_sq (h : IsRatioBasis A S) : S.card ≤ A.card ^ 2 :=
  calc S.card ≤ (A / A).card := card_le_card h
    _ ≤ A.card * A.card := card_div_le
    _ = A.card ^ 2 := (pow_two _).symm

end Finset
