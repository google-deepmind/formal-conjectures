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
# Wilf's Conjecture on Numerical Semigroups

An additive submonoid $S \le \mathbb{N}$ with finite complement $G(S) = \mathbb{N} \setminus S$
forms a *numerical semigroup*. Write
$c(S) = \min\{c \in \mathbb{N} : \forall m \ge c,\, m \in S\}$
for its conductor, $n(S) = |S \cap [0, c(S))| = c(S) - |G(S)|$ for the count of sporadic elements
below $c(S)$, and $e(S) = |S_{>0} \setminus (S_{>0} + S_{>0})|$ for its embedding dimension (the
size of its unique minimal generating set).

Herbert S. Wilf [Wi78] conjectured that $c(S) \le e(S) \cdot n(S)$ holds for all numerical
semigroups $S$ (equivalently $e(S) \ge (F(S) + 1) / (F(S) + 1 - |G(S)|)$ when $S \subsetneq
\mathbb{N}$ has largest gap $F(S) = c(S) - 1$, as stated on Wikipedia's Coin problem page).
Fröberg, Gottlieb, and Häggkvist [FGH87, Theorem 20] proved the inequality whenever $e(S) \le 3$
(sourced directly from [FGH87]); the general case remains open.

*References:*
- [Wi78] H. S. Wilf, *A circle-of-lights algorithm for the "money-changing problem"*, Amer. Math.
  Monthly **85** (1978), no. 7, 562–565, DOI: `10.1080/00029890.1978.11994639`.
- [FGH87] R. Fröberg, C. Gottlieb, and R. Häggkvist, *On numerical semigroups*, Semigroup Forum
  **35** (1987), no. 1, 63–83, DOI: `10.1007/BF02573091`.
- [Wikipedia: Coin problem — Wilf's conjecture](https://en.wikipedia.org/wiki/Coin_problem#Wilf%27s_conjecture)
-/

@[expose] public section

namespace WilfNumericalSemigroupConjecture

open AddSubmonoid

/-- Count $n(S)$ of elements in $S$ strictly below `conductor S`. -/
noncomputable def sporadicCount (S : AddSubmonoid ℕ) : ℕ :=
  open scoped Classical in
  ((Finset.range (conductor S)).filter (fun x => x ∈ S)).card

/-- On `⊤ : AddSubmonoid ℕ`, `conductor ⊤ = 0`, `sporadicCount ⊤ = 0`, and `embeddingDim ⊤ = 1`,
satisfying $0 \le 1 \cdot 0$. -/
@[category test, AMS 11 20]
theorem top_numericalSemigroup_invariants :
    IsNumericalSemigroup ⊤ ∧
      conductor ⊤ = 0 ∧
      sporadicCount ⊤ = 0 ∧
      embeddingDim ⊤ = 1 := by
  simp [sporadicCount]

/-- On $S_{2,3} = \langle 2, 3 \rangle = \mathbb{N} \setminus \{1\}$, `conductor = 2`,
`sporadicCount = 1`, and `embeddingDim = 2`, attaining equality $2 = 2 \cdot 1$. -/
@[category test, AMS 11 20]
theorem numericalSemigroup_two_three_wilf_tight :
    let S₂₃ : AddSubmonoid ℕ :=
      { carrier := {n : ℕ | n ≠ 1}, zero_mem' := Nat.zero_ne_one
        add_mem' := fun {a b} (ha : a ≠ 1) (hb : b ≠ 1) (h : a + b = 1) =>
          absurd (show a = 1 ∨ b = 1 by omega) (by tauto) }
    IsNumericalSemigroup S₂₃ ∧ conductor S₂₃ = 2 ∧
      sporadicCount S₂₃ = 1 ∧ embeddingDim S₂₃ = 2 := by
  intro S₂₃
  have hmem (n : ℕ) : n ∈ S₂₃ ↔ n ≠ 1 := Iff.rfl
  have hc2 : conductor S₂₃ = 2 := le_antisymm
    (Nat.sInf_le fun m hm => (hmem m).mpr (by omega))
    (le_csInf ⟨2, fun m hm => (hmem m).mpr (by omega)⟩ fun c hc =>
      by by_contra!; exact (hmem 1).mp (hc 1 (by omega)) rfl)
  refine ⟨by simp [IsNumericalSemigroup, show (S₂₃ : Set ℕ)ᶜ = {1} by ext; simp [hmem]],
    hc2, by classical simp [sporadicCount, hc2,
      show (Finset.range 2).filter (· ∈ S₂₃) = {0} by ext; simp [hmem]; omega], ?_⟩
  have hset : {x : ℕ | 0 < x ∧ x ∈ S₂₃ ∧
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S₂₃ ∧ b ∈ S₂₃ ∧ x = a + b} = {2, 3} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hmem]
    refine ⟨fun ⟨_, _, hmin⟩ => ?_, fun h => by rcases h with rfl | rfl <;>
      exact ⟨by omega, by omega, fun ⟨a, b, _⟩ => by omega⟩⟩
    by_cases hx : x ≤ 3; · omega
    exact (if h4 : x = 4 then hmin ⟨2, 2, by omega, by omega, by omega, by omega, by omega⟩ else
      hmin ⟨2, x - 2, by omega, by omega, by omega, by omega, by omega⟩).elim
  rw [embeddingDim, hset, Set.ncard_pair (by decide)]

/-- **Wilf's Conjecture** [Wi78]: Every numerical semigroup $S \le \mathbb{N}$ obeys
$c(S) \le e(S) \cdot n(S)$. -/
@[category research open, AMS 11 20]
theorem wilf_numerical_semigroup_conjecture {S : AddSubmonoid ℕ} (hS : IsNumericalSemigroup S) :
    conductor S ≤ embeddingDim S * sporadicCount S := by
  sorry

/-- **Fröberg–Gottlieb–Häggkvist Theorem** [FGH87, Theorem 20]: Every numerical semigroup
$S \le \mathbb{N}$ with embedding dimension $e(S) \le 3$ satisfies $c(S) \le e(S) \cdot n(S)$. -/
@[category research solved, AMS 11 20]
theorem wilf_conjecture_embedding_dim_le_three {S : AddSubmonoid ℕ} (hS : IsNumericalSemigroup S)
    (he : embeddingDim S ≤ 3) :
    conductor S ≤ embeddingDim S * sporadicCount S := by
  sorry

end WilfNumericalSemigroupConjecture
