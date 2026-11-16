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
# Erdős Problem 771

*References:*
- [erdosproblems.com/771](https://www.erdosproblems.com/771)
- [Er89] Erdős, P., *Some problems and results on combinatorial number theory*. Graph theory and
  its applications: East and West (Jinan, 1986), Ann. New York Acad. Sci. 576 (1989), 132-145.
- [AlFr88] Alon, N. and Freiman, G., *On sums of subsets of a set of integers*. Combinatorica 8
  (1988), 297-306.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos771

/-- `IsAdmissible n k` says that for every $m \geq 1$ there is a $k$-element
$S \subseteq \{1,\ldots,n\}$ such that no subset of $S$ sums to $m$. -/
def IsAdmissible (n k : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ S ⊆ Finset.Icc 1 n, S.card = k ∧ ∀ A ⊆ S, (∑ a ∈ A, a) ≠ m

/-- $f(n)$: the largest $k$ such that for every $m \geq 1$ there is a $k$-element
$S \subseteq \{1,\ldots,n\}$ with $m \neq \sum_{a \in A} a$ for all $A \subseteq S$. The set of
such $k$ contains $0$ and is bounded by $n$, so `sSup` is its maximum. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | IsAdmissible n k}

/-- $k = 0$ is always admissible. -/
@[category API, AMS 11]
theorem isAdmissible_zero (n : ℕ) : IsAdmissible n 0 := fun m hm =>
  ⟨∅, Finset.empty_subset _, Finset.card_empty, fun A hA => by
    rw [Finset.subset_empty.1 hA, Finset.sum_empty]
    omega⟩

/-- An admissible $k$ is at most $n$. -/
@[category API, AMS 11]
theorem IsAdmissible.le {n k : ℕ} (h : IsAdmissible n k) : k ≤ n := by
  obtain ⟨S, hS, rfl, -⟩ := h 1 le_rfl
  simpa using Finset.card_le_card hS

/-- Every admissible $k$ is at most $f(n)$. -/
@[category API, AMS 11]
theorem le_f {n k : ℕ} (h : IsAdmissible n k) : k ≤ f n :=
  le_csSup ⟨n, fun _ hk => IsAdmissible.le hk⟩ h

/--
Let $f(n)$ be maximal such that, for every $m\geq 1$, there exists some
$S\subseteq \{1,\ldots,n\}$ with $\lvert S\rvert=f(n)$ such that $m\neq \sum_{a\in A}a$ for all
$A\subseteq S$.

Is it true that
$$f(n) = \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}?$$

The answer is yes: the lower bound is due to Erdős and Graham and the upper bound to Alon and
Freiman [AlFr88].
-/
@[category research solved, question, AMS 11]
theorem erdos_771 :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] fun n : ℕ ↦ (n : ℝ) / (2 * Real.log n) := by
  sorry

/--
Erdős and Graham proved the lower bound
$$f(n)\geq \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}.$$
Their proof is to note that we can assume that $m< \binom{n+1}{2}$ and then, for any $m$, take
$S=\{ kp : 1\leq k<\frac{n}{p}\}$ where $p$ is the least prime that does not divide $m$
(so $p<(2+o(1))\log n$).
-/
@[category research solved, AMS 11]
theorem erdos_771.variants.erdos_graham_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 2 - ε) * ((n : ℝ) / Real.log n) ≤ f n := by
  sorry

/--
The complementary bound
$$f(n) \leq \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}$$
was proved by Alon and Freiman [AlFr88], who chose $m$ as the least common multiple of
$\{1,\ldots,s\}$ where $s$ is maximal such that $m\leq \frac{n^2}{20(\log n)^2}$.
-/
@[category research solved, AMS 11]
theorem erdos_771.variants.alon_freiman_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (1 / 2 + ε) * ((n : ℝ) / Real.log n) := by
  sorry

end Erdos771
