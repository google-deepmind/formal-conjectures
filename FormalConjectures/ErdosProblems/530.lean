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
# Erdős Problem 530

*Reference:* [Erdős Problem 530](https://www.erdosproblems.com/530)
-/

namespace Erdos530

open Filter Asymptotics

/-- `A` contains a Sidon subset of cardinality exactly `k`. -/
def HasSidonSubsetOfCard (A : Finset ℝ) (k : ℕ) : Prop :=
  ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon (S : Set ℝ) ∧ S.card = k

/-- Every $N$-element finite set of reals contains a Sidon subset of cardinality $k$. -/
def UniformSidonSubsetSize (N k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N → HasSidonSubsetOfCard A k

/-- The largest $k$ such that every $N$-element finite set of reals contains a Sidon subset of
cardinality $k$. -/
noncomputable def ell (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (UniformSidonSubsetSize N) N

local notation "ℓ" => ell

/--
`A` can be written as a union of at most `k` Sidon subsets of `A`.
The Sidon pieces are not required to be disjoint, matching the phrase
"written as the union".
-/
def HasSidonCoverOfCardAtMost (A : Finset ℝ) (k : ℕ) : Prop :=
  ∃ C : Finset (Finset ℝ),
    C.card ≤ k ∧ (∀ S ∈ C, S ⊆ A ∧ IsSidon (S : Set ℝ)) ∧ C.biUnion id = A

/-- `k` Sidon sets always suffice to cover every `N`-element finite real set. -/
def UniformSidonCoverBound (N k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N → HasSidonCoverOfCardAtMost A k

/-- Let $\ell(N)$ be maximal such that every $N$-element finite set of reals contains a Sidon
subset of cardinality $\ell(N)$. Komlós, Sulyok, and Szemerédi proved that
$\ell(N) = \Theta(\sqrt N)$. -/
@[category research solved, AMS 5 11]
theorem erdos_530.parts.i :
    (fun N : ℕ => (ℓ N : ℝ)) =Θ[atTop] (fun N : ℕ => (N : ℝ).sqrt) := by
  sorry

/-- Is $\ell(N) \sim \sqrt N$? -/
@[category research open, AMS 5 11]
theorem erdos_530.parts.ii : answer(sorry) ↔
    (fun N : ℕ => (ℓ N : ℝ)) ~[atTop] (fun N : ℕ => (N : ℝ).sqrt) := by
  sorry

/-- Alon and Erdős asked whether every $N$-element finite set of reals can be written as the
union of at most $(1 + o(1))\sqrt N$ Sidon sets. -/
@[category research open, AMS 5 11]
theorem erdos_530.variants.alon_erdos : answer(sorry) ↔ ∃ K : ℕ → ℕ,
    (∀ N, UniformSidonCoverBound N (K N)) ∧
    ∀ ε > 0, ∀ᶠ N in atTop, (K N : ℝ) ≤ (1 + ε) * (N : ℝ).sqrt := by
  sorry

end Erdos530
