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
# Erdős Problem 840

*Reference:* [erdosproblems.com/840](https://www.erdosproblems.com/840)

Let $f(N)$ be the size of the largest quasi-Sidon subset $A \subset \{1, \ldots, N\}$,
where we say that $A$ is quasi-Sidon if $|A + A| = (1 + o(1))\binom{|A|}{2}$.
How does $f(N)$ grow?

Erdős and Freud [ErFr91] proved
$(2/\sqrt{3} + o(1))N^{1/2} \leq f(N) \leq (2 + o(1))N^{1/2}$.

The upper bound was improved by Pikhurko [Pi06] to
$f(N) \leq ((1/4 + 1/(\pi+2)^2)^{-1/2} + o(1))N^{1/2} \approx 1.863\, N^{1/2}$.

[Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_.
Analytic number theory (Philadelphia, Pa., 1980), 1981, pp. 171–182.

[ErFr91] Erdős, P. and Freud, R., _On sums of a Sidon-sequence_. J. Number Theory (1991),
196–205.

[Er92c] Erdős, P., _Some of my favourite problems in various branches of combinatorics_,
Matematiche (Catania) **47** (1992), no. 2, 231–240.

[Pi06] Pikhurko, O., _Dense edge-magic graphs and thin additive bases_. Discrete Mathematics
(2006), 2097–2107.
-/

open Finset Classical

open scoped Pointwise

namespace Erdos840

/-- A finite set of natural numbers is $\delta$-quasi-Sidon if
$|A + A| \geq (1 - \delta) \cdot \binom{|A|}{2}$.
A sequence of sets is quasi-Sidon iff for every $\delta > 0$ it is eventually
$\delta$-quasi-Sidon. -/
def IsQuasiSidon (δ : ℝ) (A : Finset ℕ) : Prop :=
  ((A + A).card : ℝ) ≥ (1 - δ) * (Nat.choose A.card 2 : ℝ)

/-- The maximum size of a $\delta$-quasi-Sidon subset of $\{1, \ldots, N\}$. -/
noncomputable def maxQuasiSidonCard (δ : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => IsQuasiSidon δ A)).sup Finset.card

/--
**Erdős Problem 840** — How does $f(N)$ grow?

The problem asks for the asymptotic constant $c$ such that
$f_\delta(N) \sim c \cdot \sqrt{N}$ as $N \to \infty$, where $f(N)$ is the size of
the largest quasi-Sidon subset of $\{1, \ldots, N\}$.
It is known that $2/\sqrt{3} \leq c \leq (1/4 + 1/(\pi+2)^2)^{-1/2} \approx 1.863$.
-/
@[category research open, AMS 5 11]
theorem erdos_840 :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |(maxQuasiSidonCard δ N : ℝ) - answer(sorry) * Real.sqrt (N : ℝ)| ≤
      ε * Real.sqrt (N : ℝ) := by
  sorry

/--
**Erdős Problem 840** — Lower bound (Erdős–Freud [ErFr91]):

For every $\varepsilon > 0$ and $\delta > 0$, for sufficiently large $N$,
$f_\delta(N) \geq (2/\sqrt{3} - \varepsilon) \cdot \sqrt{N}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_840.variants.lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxQuasiSidonCard δ N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ) := by
  sorry

/--
**Erdős Problem 840** — Upper bound (Pikhurko [Pi06]):

For every $\varepsilon > 0$ and $\delta > 0$, for sufficiently large $N$,
$f_\delta(N) \leq ((1/4 + 1/(\pi+2)^2)^{-1/2} + \varepsilon) \cdot \sqrt{N}$.

The constant $(1/4 + 1/(\pi+2)^2)^{-1/2} \approx 1.863$.
-/
@[category research solved, AMS 5 11]
theorem erdos_840.variants.upper_bound :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxQuasiSidonCard δ N : ℝ) ≤
      (Real.sqrt ((1 / 4 + 1 / (Real.pi + 2) ^ 2)⁻¹) + ε) * Real.sqrt (N : ℝ) := by
  sorry

end Erdos840
