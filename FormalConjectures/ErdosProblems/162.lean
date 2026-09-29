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
# Erdős Problem 162

*References:*
- [erdosproblems.com/162](https://www.erdosproblems.com/162)
- [Er90b] Erdős, Paul, *Problems and results on graphs and hypergraphs: similarities and
  differences*. Mathematics of Ramsey theory (1990), 12-28.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos162

/-- The number of edges of $K_n$ inside `H` that get colour `b` under the colouring `c`. -/
def colourEdgeCount {n : ℕ} (c : Sym2 (Fin n) → Bool) (H : Finset (Fin n)) (b : Bool) : ℕ :=
  (H.sym2.filter (fun e ↦ ¬ e.IsDiag ∧ c e = b)).card

/-- Every set `H` of at least `k` vertices contains more than $\alpha\binom{|H|}{2}$ edges of
each colour under `c`. -/
def IsBalancedAbove (n : ℕ) (α : ℝ) (c : Sym2 (Fin n) → Bool) (k : ℕ) : Prop :=
  ∀ H : Finset (Fin n), k ≤ H.card → ∀ b : Bool,
    α * (H.card.choose 2 : ℝ) < colourEdgeCount c H b

/-- $F(n, \alpha)$: the smallest `k` such that some 2-colouring of $K_n$ satisfies
`IsBalancedAbove n α c k`.

The source says "largest `k`". Read literally, every `k > n` works vacuously, so no largest `k`
exists. The smallest `k` is the reading consistent with the stated $\Theta(\log n)$ growth. -/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ c : Sym2 (Fin n) → Bool, IsBalancedAbove n α c k}

/--
Let $\alpha > 0$ and $n \geq 1$. Let $F(n,\alpha)$ be the largest $k$ such that there exists some
2-colouring of the edges of $K_n$ in which any induced subgraph $H$ on at least $k$ vertices
contains more than $\alpha\binom{|H|}{2}$ many edges of each colour.

Prove that for every fixed $0 \leq \alpha \leq 1/2$, as $n \to \infty$,
$F(n,\alpha) \sim c_\alpha \log n$ for some constant $c_\alpha$.

We require $\alpha < 1/2$: at $\alpha = 1/2$ no colouring works for any `k ≤ n`
(see `erdos_162.variants.half`).
-/
@[category research open, AMS 5]
theorem erdos_162 (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    ∃ c : ℝ, (fun n : ℕ ↦ (F n α : ℝ)) ~[atTop] (fun n : ℕ ↦ c * Real.log n) := by
  sorry

/--
It is easy to show with the probabilistic method that there exist $c_1(\alpha), c_2(\alpha)$ such
that $c_1(\alpha)\log n < F(n,\alpha) < c_2(\alpha)\log n$.
-/
@[category research solved, AMS 5]
theorem erdos_162.variants.bounds (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n := by
  sorry

/--
At $\alpha = 1/2$ the two colour counts in $H$ add up to $\binom{|H|}{2}$, so both cannot exceed
half of it. Hence $F(n, 1/2) = n + 1$, and the claim fails at $\alpha = 1/2$.
-/
@[category textbook, AMS 5]
theorem erdos_162.variants.half (n : ℕ) : F n (1 / 2) = n + 1 := by
  sorry

/-- `k = n + 1` always works, since no vertex set has more than `n` elements. -/
@[category API, AMS 5]
theorem isBalancedAbove_succ (n : ℕ) (α : ℝ) (c : Sym2 (Fin n) → Bool) :
    IsBalancedAbove n α c (n + 1) := by
  intro H hH
  have := H.card_le_univ
  simp at this
  omega

/-- $F(n, \alpha)$ is at most `n + 1`. -/
@[category API, AMS 5]
theorem F_le_succ (n : ℕ) (α : ℝ) : F n α ≤ n + 1 :=
  Nat.sInf_le ⟨fun _ ↦ true, isBalancedAbove_succ n α _⟩

end Erdos162
