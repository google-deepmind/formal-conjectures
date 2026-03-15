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
# Erdős Problem 84

*Reference:* [erdosproblems.com/84](https://www.erdosproblems.com/84)

The cycle set of a graph $G$ on $n$ vertices is the set $A \subseteq \{3, \ldots, n\}$ of all cycle
lengths present in $G$. Let $f(n)$ count the number of distinct such sets $A$ over all graphs on
$n$ vertices. Erdős and Faudree conjectured that $f(n) = o(2^n)$ and $f(n) / 2^{n/2} \to \infty$.

Erdős and Faudree showed $2^{n/2} < f(n) \leq 2^{n-2}$.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Discrete Math. 165/166 (1997), 227–231.

[Er95] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. 164 (1997), 81–85.

[Er96] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) 47 (1992), 231–240.

[Er97d] Erdős, P., _Some problems and results in combinatorial number theory_.

[Ve04] Verstraëte, J., _On the number of sets of cycle lengths_.
Combinatorica (2004), 719–730.

[Ne25] Nenadov, R., _Improved bound on the number of cycle sets_.
arXiv:2501.09904 (2025).
-/

open SimpleGraph

namespace Erdos84

/-- The cycle spectrum of a simple graph: the set of all cycle lengths present in $G$. -/
def cycleSpectrum {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = ℓ}

/-- The number of distinct cycle spectra realizable by simple graphs on $\operatorname{Fin}(n)$. -/
noncomputable def cycleSetCount (n : ℕ) : ℕ :=
  Set.ncard {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSpectrum G = A}

/--
Erdős Problem 84, Part 2 (open) [Er94b][Er95][Er96][Er97d]:
$f(n) / 2^{n/2} \to \infty$.
That is, for every $B > 0$, for all sufficiently large $n$, $f(n) \geq B \cdot 2^{n/2}$.

This is the main open conjecture; Part 1 (the solved upper bound) appears below as a variant.
-/
@[category research open, AMS 5]
theorem erdos_84 :
    ∀ B : ℝ, B > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount n : ℝ) ≥ B * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

/--
Erdős Problem 84, Part 1 (proved by Verstraëte [Ve04]):
$f(n) = o(2^n)$.
That is, for every $\varepsilon > 0$, for all sufficiently large $n$,
$f(n) \leq \varepsilon \cdot 2^n$.

Verstraëte proved $f(n) \ll 2^{n - n^{1/10}}$, improved by Nenadov to
$f(n) \ll 2^{n - n^{1/2 - o(1)}}$.
-/
@[category research solved, AMS 5]
theorem erdos_84.variants.subexponential :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount n : ℝ) ≤ ε * (2 : ℝ) ^ n := by
  sorry

/--
Erdős Problem 84, variant: does $\lim_{n \to \infty} f(n)^{1/n}$ exist, and if so, what is its
value? This is noted as an open question on the website.
-/
@[category research open, AMS 5]
theorem erdos_84.variants.limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n => (cycleSetCount n : ℝ) ^ ((1 : ℝ) / n))
      Filter.atTop (nhds L) := by
  sorry

end Erdos84
