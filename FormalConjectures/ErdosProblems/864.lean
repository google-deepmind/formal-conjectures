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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 864

*Reference:* [erdosproblems.com/864](https://www.erdosproblems.com/864)

Let $A\subseteq \{1,\ldots, N\}$ be a set such that there exists at most one $n$
with more than one solution to $n = a + b$ (with $a \le b \in A$).
Estimate the maximal possible size of $|A|$ — in particular, is it true that
$|A| \le (1+o(1))\frac{2}{\sqrt{3}} N^{1/2}$?

A problem of Erdős and Freud [ErFr91], who prove the matching lower bound
$|A| \ge (1+o(1))\frac{2}{\sqrt{3}} N^{1/2}$.

This is a weaker form of Problem 840.

[ErFr91] Erdős, P. and Freud, R., *On Sidon-sequences and related problems*, 1991.
-/

open Finset Classical

namespace Erdos864

/-- The number of representations of $n$ as $a + b$ with $a \le b$, $a \in A$, $b \in A$. -/
def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun a => 2 * a ≤ n ∧ (n - a) ∈ A)).card

/-- A set $A$ is *almost Sidon* if at most one integer $n$ has more than one
    representation as $n = a + b$ with $a \le b \in A$. -/
def IsAlmostSidon (A : Finset ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card ≤ 1 ∧
    ∀ n : ℕ, n ∉ S → sumRepCount A n ≤ 1

/-- The maximum size of an almost Sidon subset of $\{1, \ldots, N\}$. -/
noncomputable def maxAlmostSidonCard (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter IsAlmostSidon).sup Finset.card

/--
**Erdős Problem 864** [ErFr91] — Is it true that for every $\varepsilon > 0$,
for sufficiently large $N$,
$$f(N) \le \left(\frac{2}{\sqrt{3}} + \varepsilon\right) \sqrt{N}?$$
-/
@[category research open, AMS 5 11]
theorem erdos_864 : answer(sorry) ↔
    (∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxAlmostSidonCard N : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt (N : ℝ)) := by
  sorry

/--
**Erdős Problem 864** — Lower bound (Erdős–Freud [ErFr91]):

For every $\varepsilon > 0$, for sufficiently large $N$,
$$f(N) \ge \left(\frac{2}{\sqrt{3}} - \varepsilon\right) \sqrt{N}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_864.variants.lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxAlmostSidonCard N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ) := by
  sorry

end Erdos864
