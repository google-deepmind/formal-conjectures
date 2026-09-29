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
# Erdős Problem 161

*References:*
- [erdosproblems.com/161](https://www.erdosproblems.com/161)
- [Er90b] Erdős, Paul, *Problems and results on graphs and hypergraphs: similarities and
  differences*. Mathematics of Ramsey theory (1990), 12-28.
- [CFS11] Conlon, D. and Fox, J. and Sudakov, B., *Large almost monochromatic subsets in
  hypergraphs*. Israel J. Math. (2011), 423-432.
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos161

/-- The number of `t`-subsets of `X` that receive colour `b` under the colouring `c`. -/
def colourCount {n : ℕ} (t : ℕ) (c : Finset (Fin n) → Bool) (X : Finset (Fin n)) (b : Bool) :
    ℕ :=
  ((X.powersetCard t).filter (fun Y ↦ c Y = b)).card

/-- `X` is *balanced* for the colouring `c`: each colour occurs on at least one and on at least
$\alpha\binom{|X|}{t}$ of the `t`-subsets of `X`. Requiring at least one makes the case
$\alpha = 0$ the usual Ramsey condition (see `admissible_zero_iff`). -/
def Balanced {n : ℕ} (t : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) (X : Finset (Fin n)) : Prop :=
  ∀ b : Bool, 0 < colourCount t c X b ∧ α * (X.card.choose t : ℝ) ≤ colourCount t c X b

/-- `m` is admissible if some 2-colouring of the `t`-subsets of `Fin n` makes every `X` with
`m ≤ |X|` balanced. -/
def Admissible (t n : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card → Balanced t α c X

/-- $F^{(t)}(n, \alpha)$: the smallest admissible `m`. -/
noncomputable def F (t n : ℕ) (α : ℝ) : ℕ :=
  sInf {m | Admissible t n α m}

/--
Let $\alpha\in[0,1/2)$ and $n,t\geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that we
can $2$-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that if
$X\subseteq[n]$ with $|X|\geq m$ then there are at least $\alpha\binom{|X|}{t}$ many $t$-subsets of
$X$ of each colour.

For fixed $n,t$, as we change $\alpha$ from $0$ to $1/2$, does $F^{(t)}(n,\alpha)$ increase
continuously or are there jumps? Only one jump?

Erdős guessed that the jump occurs all in one step at $0$ [Er90b]. We state this guess
asymptotically in $n$: for $0 < \alpha \leq \beta < 1/2$,
$F^{(t)}(n,\alpha) \asymp F^{(t)}(n,\beta)$.
-/
@[category research open, AMS 5]
theorem erdos_161 : answer(sorry) ↔
    ∀ t : ℕ, 1 ≤ t → ∀ α β : ℝ, 0 < α → α ≤ β → β < 1 / 2 →
      (fun n ↦ (F t n β : ℝ)) =Θ[atTop] (fun n ↦ (F t n α : ℝ)) := by
  sorry

/--
For $t = 3$ there is only one jump, at $\alpha = 0$: Conlon, Fox and Sudakov [CFS11] proved
$F^{(3)}(n,\alpha) \ll_\alpha \sqrt{\log n}$, which matches the lower bound of Erdős and Spencer.
-/
@[category research solved, AMS 5]
theorem erdos_161.variants.three : ∀ α β : ℝ, 0 < α → α ≤ β → β < 1 / 2 →
    (fun n ↦ (F 3 n β : ℝ)) =Θ[atTop] (fun n ↦ (F 3 n α : ℝ)) := by
  sorry

/-- `n + 1` is always admissible (vacuously). -/
@[category API, AMS 5]
theorem admissible_succ (t n : ℕ) (α : ℝ) : Admissible t n α (n + 1) := by
  refine ⟨fun _ ↦ true, fun X hX ↦ ?_⟩
  have := X.card_le_univ
  simp at this
  omega

/-- $F^{(t)}(n, \alpha)$ is well defined and at most `n + 1`. -/
@[category API, AMS 5]
theorem F_le (t n : ℕ) (α : ℝ) : F t n α ≤ n + 1 :=
  Nat.sInf_le (admissible_succ t n α)

/-- For $\alpha = 0$, admissibility is the Ramsey condition: some colouring has no monochromatic
`m`-set. -/
@[category API, AMS 5]
theorem admissible_zero_iff {t n m : ℕ} :
    Admissible t n 0 m ↔ ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), X.card = m →
      ∀ b : Bool, ∃ Y ⊆ X, Y.card = t ∧ c Y = b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun X hX b ↦ ?_⟩
    obtain ⟨Y, hY⟩ := Finset.card_pos.1 (hc X hX.ge b).1
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hY
    exact ⟨Y, hY.1.1, hY.1.2, hY.2⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun X hX b ↦ ⟨?_, by simp⟩⟩
    obtain ⟨Z, hZX, hZ⟩ := Finset.exists_subset_card_eq hX
    obtain ⟨Y, hYZ, hY, hcY⟩ := hc Z hZ b
    exact Finset.card_pos.2 ⟨Y, by simp [colourCount, hYZ.trans hZX, hY, hcY]⟩

end Erdos161
