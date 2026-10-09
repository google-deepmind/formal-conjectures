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
# Erdős Problem 864

*References:*
- [erdosproblems.com/864](https://www.erdosproblems.com/864)
- [A389182](https://oeis.org/A389182)
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196--205.
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. 15
  (1992), 34-50.
-/

@[expose] public section

open Filter
open scoped Finset

namespace Erdos864

/-- The representations of $n$ as a sum $n = a + b$ with $a \leq b$ and $a, b \in A$, recorded as
the pairs $(a, b)$. The case $a = b$ is allowed. -/
def sumRepresentations (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ A ×ˢ A | p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/-- There is at most one $n$ with more than one representation $n = a + b$, where $a \leq b$ and
$a, b \in A$. That is, any two integers with more than one representation are equal.

Every Sidon set satisfies this condition, since then no $n$ has more than one representation. -/
def HasAtMostOneRepeatedSum (A : Finset ℕ) : Prop :=
  ∀ n m : ℕ, 1 < #(sumRepresentations A n) → 1 < #(sumRepresentations A m) → n = m

/--
Let $A\subseteq \{1,\ldots,N\}$ be a set such that there exists at most one $n$ with more than one
solution to $n=a+b$ (with $a\leq b\in A$). Estimate the maximal possible size of $|A|$. In
particular, is it true that
$$|A| \leq (1+o(1))\frac{2}{\sqrt{3}} N^{1/2}?$$

A problem of Erdős and Freud [ErFr91] [Er92c]. For the analogous question with $n=a-b$ they prove
that $\lvert A\rvert\sim N^{1/2}$. This is a weaker form of Erdős Problem 840.

The condition on $A$ is `HasAtMostOneRepeatedSum`. We state the question as follows: for every
$\varepsilon > 0$ and all large $N$, every such set $A$ satisfies
$|A| \leq (1+\varepsilon)\frac{2}{\sqrt{3}} N^{1/2}$.
-/
@[category research open, AMS 5 11]
theorem erdos_864 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      HasAtMostOneRepeatedSum A →
        (#A : ℝ) ≤ (1 + ε) * (2 / Real.sqrt 3) * Real.sqrt (N : ℝ) := by
  sorry

/--
Erdős and Freud [ErFr91] [Er92c] prove that
$$\lvert A\rvert \geq (1+o(1))\frac{2}{\sqrt{3}}N^{1/2}.$$
This is shown by taking a genuine Sidon set $B\subset [1,N/3]$ of size $\sim N^{1/2}/\sqrt{3}$
and taking the union with $\{N-b : b\in B\}$.

That is, for every $\varepsilon > 0$ and all large $N$ there is a set $A\subseteq \{1,\ldots,N\}$
with the property of `Erdos864.erdos_864` and $|A| \geq (1-\varepsilon)\frac{2}{\sqrt{3}}N^{1/2}$.
So the constant $2/\sqrt{3}$ there cannot be replaced by a smaller one.
-/
@[category research solved, AMS 5 11]
theorem erdos_864.variants.lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Finset.Icc 1 N,
      HasAtMostOneRepeatedSum A ∧
        (1 - ε) * (2 / Real.sqrt 3) * Real.sqrt (N : ℝ) ≤ #A := by
  sorry

/-- A Sidon set has no integer with more than one representation, so it satisfies the condition
of the problem. -/
@[category test, AMS 5 11]
theorem hasAtMostOneRepeatedSum_of_isSidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    HasAtMostOneRepeatedSum A := by
  intro n m hn _
  exfalso
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hn
  simp only [sumRepresentations, Finset.mem_filter, Finset.mem_product] at hp hq
  obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
  rcases hA p.1 (Finset.mem_coe.2 hp1) q.1 (Finset.mem_coe.2 hq1)
      p.2 (Finset.mem_coe.2 hp2) q.2 (Finset.mem_coe.2 hq2) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hpq (Prod.ext h1 h2)
  · exact hpq (Prod.ext (by omega) (by omega))

/-- The set $\{1,2,3\}$ is not a Sidon set, but it satisfies the condition: only
$4 = 1 + 3 = 2 + 2$ has two representations. -/
@[category test, AMS 5 11]
theorem hasAtMostOneRepeatedSum_one_two_three : HasAtMostOneRepeatedSum {1, 2, 3} := by
  have key : ∀ n, 1 < #(sumRepresentations {1, 2, 3} n) → n = 4 := by
    intro n hn
    obtain ⟨⟨a, b⟩, hp, ⟨c, d⟩, hq, hpq⟩ := Finset.one_lt_card.1 hn
    simp only [sumRepresentations, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton] at hp hq
    have hne : a ≠ c ∨ b ≠ d := by
      rw [Ne, Prod.mk.injEq, not_and_or] at hpq
      exact hpq
    omega
  intro n m hn hm
  rw [key n hn, key m hm]

/-- The set $\{1,2,3,4\}$ does not satisfy the condition: both $4 = 1 + 3 = 2 + 2$ and
$5 = 1 + 4 = 2 + 3$ have two representations. Without the case $a = b$, $4$ would have only one
representation and the set would satisfy the condition. -/
@[category test, AMS 5 11]
theorem not_hasAtMostOneRepeatedSum_Icc_one_four :
    ¬ HasAtMostOneRepeatedSum (Finset.Icc 1 4) := by
  intro h
  have h4 : 1 < #(sumRepresentations (Finset.Icc 1 4) 4) := by decide +kernel
  have h5 : 1 < #(sumRepresentations (Finset.Icc 1 4) 5) := by decide +kernel
  have := h 4 5 h4 h5
  omega

end Erdos864
