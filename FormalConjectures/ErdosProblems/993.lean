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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 993

*Reference:* [erdosproblems.com/993](https://www.erdosproblems.com/993)

Alavi, Erdős, Malde, and Schwenk (1987) conjectured that the *independent set
sequence* of every tree — and, more generally, of every forest — is unimodal.
Here, for a finite graph `G`, the independent set sequence is `i₀, i₁, …`, where
`iₖ` is the number of independent sets of `G` of cardinality `k`. A sequence is
unimodal if it is nondecreasing up to some index and nonincreasing thereafter.

The conjecture is *false* for general graphs (there are graphs whose independent
set sequence has an interior valley), but it remains **open** for forests.

[AEMS87] Y. Alavi, P. J. Erdős, P. J. Malde, A. J. Schwenk,
*The vertex independence sequence of a graph is not constrained*,
Congressus Numerantium 58 (1987), 15–23.
-/

namespace Erdos993

/-- The number of independent sets of cardinality `k` in a finite graph `G`
(the `k`-th term of the independent set sequence). -/
noncomputable def numIndepSets {α : Type*} [Fintype α] (G : SimpleGraph α)
    (k : ℕ) : ℕ :=
  Nat.card {s : Finset α // G.IsIndepSet (s : Set α) ∧ s.card = k}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index
`m` and nonincreasing from `m` on. -/
def Unimodal (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧ (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

/--
The independent set sequence of every finite forest (acyclic graph) is unimodal.
Since a tree is a connected forest, this includes the tree case.
[Alavi, Erdős, Malde, Schwenk, 1987]
-/
@[category research open, AMS 5]
theorem erdos_993 : ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    G.IsAcyclic → Unimodal (numIndepSets G) := by
  sorry

end Erdos993
