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
# Erdős Problem 670

*References:*
- [erdosproblems.com/670](https://www.erdosproblems.com/670)
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [Ho26] Ho, B. S., *Erdős's diameter conjecture for separated distances fails in high
  dimensions*. [arXiv:2604.15305](https://arxiv.org/abs/2604.15305) (2026).
-/

@[expose] public section

open Filter

namespace Erdos670

/-- A finite set $A$ of points has *separated distances* if all its pairwise distances differ
by at least $1$: for any two different unordered pairs $\{a, b\} \neq \{c, e\}$ of distinct
points of $A$, we have $\lvert d(a, b) - d(c, e)\rvert \geq 1$. -/
def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/--
Let $A\subseteq \mathbb{R}^d$ be a set of $n$ points such that all pairwise distances differ by
at least $1$. Is the diameter of $A$ at least $(1+o(1))n^2$?

The quantifiers in the source are ambiguous. Following the remarks on erdosproblems.com, this is
the regime where $d$ is fixed and the $o(1)$ term tends to $0$ as $n \to \infty$, at a rate
which may depend on $d$. The case $d = 1$ was proved by Erdős
(`Erdos670.erdos_670.variants.dim_one`), so the question is open for $d \geq 2$.
-/
@[category research open, AMS 52]
theorem erdos_670 : answer(sorry) ↔
    ∀ d : ℕ, 1 ≤ d → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  sorry

/--
Erdős [Er97f] proved the claim when $d = 1$: if $A\subseteq \mathbb{R}$ is a set of $n$ points
such that all pairwise distances differ by at least $1$, then the diameter of $A$ is at least
$(1+o(1))n^2$.
-/
@[category research solved, AMS 52]
theorem erdos_670.variants.dim_one : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 1)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1))) := by
  sorry

/--
The trivial lower bound: if $A\subseteq \mathbb{R}^d$ is a set of $n \neq 2$ points such that all
pairwise distances differ by at least $1$, then the diameter of $A$ is at least $\binom{n}{2}$.

For $n \geq 3$, take a closest pair $a, b$ and a third point $c$. Then
$1 \leq \lvert d(a, c) - d(b, c)\rvert \leq d(a, b)$, so every distance is at least $1$. The
$\binom{n}{2}$ distances are at least $1$ apart, so the largest one is at least $\binom{n}{2}$.
For $n = 2$ the hypothesis is vacuous, and two points at distance $1/2$ show that the bound fails.
-/
@[category textbook, AMS 52]
theorem erdos_670.variants.choose_two (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : HasSeparatedDistances A) (hn : A.card ≠ 2) :
    (A.card.choose 2 : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  sorry

/--
Ho [Ho26] showed that the claim fails if $n$ grows with $d$: there exist infinitely many $n$
and, with $d = n^2 - n$, a set $A\subset \mathbb{R}^d$ of $n$ points such that all pairwise
distances differ by at least $1$, with diameter at most
$$
\left(1-\frac{1}{\pi^2}+o(1)\right)n^2\approx 0.898n^2.
$$
Ho's construction uses $n = q + 1$ points in dimension $q^2 + q = n^2 - n$, for every prime power
$q$.
-/
@[category research solved, AMS 52]
theorem erdos_670.variants.ho :
    ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin (n ^ 2 - n))), A.card = n ∧
        HasSeparatedDistances A ∧
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin (n ^ 2 - n)))) ≤
          (1 - 1 / Real.pi ^ 2 + ε) * (n : ℝ) ^ 2 := by
  sorry

/--
The version of the problem where the $o(1)$ term must be uniform in the dimension $d$ has a
negative answer. This follows from `Erdos670.erdos_670.variants.ho` (Ho [Ho26]).
-/
@[category research solved, AMS 52]
theorem erdos_670.variants.uniform_in_dim : answer(False) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  sorry

end Erdos670
