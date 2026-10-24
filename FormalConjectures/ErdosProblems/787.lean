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
# Erdős Problem 787

*References:*
- [erdosproblems.com/787](https://www.erdosproblems.com/787)
- [Be25] Beker, A., *The Erdős-Moser sum-free set problem via improved bounds for
  $k$-configurations*. [arXiv:2501.10203](https://arxiv.org/abs/2501.10203) (2025).
- [Ch71] Choi, S. L. G., *On a combinatorial problem in number theory*.
  Proc. London Math. Soc. (3) (1971), 629-642.
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189. [PDF](https://www.renyi.hu/~p_erdos/1965-02.pdf)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
  1971) (1973), 117-138. [PDF](https://www.renyi.hu/~p_erdos/1973-21.pdf)
- [Ru05] Ruzsa, Imre Z., *Sum-avoiding subsets*. Ramanujan J. (2005), 77-82.
- [Sa21] Sanders, Tom, *The Erdős-Moser sum-free set problem*. Canad. J. Math. (2021), 63-107.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos787

/--
`g G n` is the largest `m` such that every set `A` of `n` elements of `G` has a subset `B` with
$\lvert B\rvert \geq m$ and $b_1 + b_2 \notin A$ for all distinct $b_1, b_2 \in B$
[Er65, p. 187]. The problem takes `G = ℝ`.

The condition on `B` is `Disjoint B.restrictedSumset A`. For `G = ℝ` or `G = ℤ`, the set of such
`m` contains `0` and is bounded by `n`, so `sSup` is its maximum, not a junk value.
-/
noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

/-- `Disjoint B.restrictedSumset A` says that $b_1 + b_2 \notin A$ for all distinct
$b_1, b_2 \in B$. -/
@[category API, AMS 5 11]
theorem disjoint_restrictedSumset_iff {G : Type*} [Add G] [DecidableEq G] (A B : Finset G) :
    Disjoint B.restrictedSumset A ↔ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A := by
  unfold Finset.restrictedSumset
  rw [Finset.disjoint_left]
  constructor
  · intro h b₁ hb₁ b₂ hb₂ hne hmem
    have hmem' : b₁ + b₂ ∈ Finset.image (fun p : G × G => p.1 + p.2) B.offDiag :=
      Finset.mem_image.2 ⟨(b₁, b₂), Finset.mem_offDiag.2 ⟨hb₁, hb₂, hne⟩, rfl⟩
    exact h hmem' hmem
  · intro h x hx hxA
    obtain ⟨⟨b₁, b₂⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hb₁, hb₂, hne⟩ := Finset.mem_offDiag.1 hp
    exact h b₁ hb₁ b₂ hb₂ hne hxA

/-- If every set of `n` reals has a subset `B` of size at least `m` with
`Disjoint B.restrictedSumset A`, then `m ≤ g ℝ n`. -/
@[category API, AMS 5 11]
theorem le_g {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) : m ≤ g ℝ n := by
  refine le_csSup (bddAbove_def.2 ⟨n, fun m' hm' => ?_⟩) h
  have hm'' : ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, m' ≤ B.card ∧ Disjoint B.restrictedSumset A := hm'
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm'' A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans_eq hA)

def erdos_787.answer : ℕ → ℝ := sorry

/--
Let $g(n)$ be maximal such that given any set $A\subset \mathbb{R}$ with $\lvert A\rvert=n$ there
exists some $B\subseteq A$ of size $\lvert B\rvert\geq g(n)$ such that $b_1+b_2\not\in A$ for all
$b_1\neq b_2\in B$.

Estimate $g(n)$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_787 : (fun n ↦ (g ℝ n : ℝ)) =Θ[atTop] erdos_787.answer := by
  sorry

/--
This function was considered by Erdős and Moser. Choi observed that, without loss of generality,
one can assume that $A\subset \mathbb{Z}$.

Here this means that sets of integers give the same value $g(n)$ as sets of reals.
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.integers (n : ℕ) : g ℤ n = g ℝ n := by
  sorry

/--
Klarner proved $g(n) \gg \log n$ (indeed, a greedy construction suffices).
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.klarner :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (g ℝ n : ℝ) := by
  sorry

/--
Choi [Ch71] proved $g(n) \ll n^{2/5+o(1)}$.

Here this means that $g(n) \leq n^{2/5+\varepsilon}$ for every $\varepsilon > 0$ and all large $n$,
as in [Er73, p. 130].
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.choi :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (g ℝ n : ℝ) ≤ (n : ℝ) ^ (2 / 5 + ε) := by
  sorry

/--
The current best bounds known are
$$(\log n)^{1+c} \ll g(n) \ll \exp(\sqrt{\log n})$$
for some constant $c>0$, the lower bound due to Sanders [Sa21] and the upper bound due to
Ruzsa [Ru05].

This is the lower bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.sanders :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Real.log n ^ (1 + c) ≤ (g ℝ n : ℝ) := by
  sorry

/--
The current best bounds known are
$$(\log n)^{1+c} \ll g(n) \ll \exp(\sqrt{\log n})$$
for some constant $c>0$, the lower bound due to Sanders [Sa21] and the upper bound due to
Ruzsa [Ru05].

This is the upper bound. [Ru05] proves it in the form $\exp(O(\sqrt{\log n}))$, which is the form
stated here.
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.ruzsa :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (g ℝ n : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) := by
  sorry

/--
Beker [Be25] has proved
$$(\log n)^{1+\tfrac{1}{68}+o(1)} \ll g(n).$$

Here this means that $g(n) \geq (\log n)^{1+c}$ for every $c < 1/68$ and all large $n$
[Be25, Theorem 1.2].
-/
@[category research solved, AMS 5 11]
theorem erdos_787.variants.beker :
    ∀ c : ℝ, 0 < c → c < 1 / 68 → ∀ᶠ n : ℕ in atTop, Real.log n ^ (1 + c) ≤ (g ℝ n : ℝ) := by
  sorry

end Erdos787
