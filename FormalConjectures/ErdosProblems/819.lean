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
# Erdős Problem 819

*Reference:* [erdosproblems.com/819](https://www.erdosproblems.com/819)

Let $f(N)$ be maximal such that there exists $A\subseteq \{1,\ldots,N\}$ with
$|A|=\lfloor N^{1/2}\rfloor$ such that $|(A+A)\cap [1,N]|=f(N)$. Estimate $f(N)$.

Erdős and Freud [ErFr91] proved
$(3/8-o(1))N \leq f(N) \leq (1/2+o(1))N$,
and note that it is closely connected to the size of the largest quasi-Sidon set
(see [840]).

[ErFr91] Erdős, P. and Freud, R.
-/

open Finset

open scoped Pointwise

namespace Erdos819

/-- The maximum of $|(A + A) \cap \{1, \ldots, N\}|$ over all $A \subseteq \{1, \ldots, N\}$ with
$|A| = \lfloor\sqrt{N}\rfloor$. -/
noncomputable def f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => A.card = Nat.sqrt N)).sup
    (fun A => ((A + A) ∩ Finset.Icc 1 N).card)

/--
**Erdős Problem 819** — Lower bound (Erdős–Freud [ErFr91]):

For every $\varepsilon > 0$, for sufficiently large $N$,
$f(N) \geq (3/8 - \varepsilon) N$.
-/
@[category research solved, AMS 5]
theorem erdos_819 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (↑(f N) : ℝ) ≥ (3 / 8 - ε) * (↑N : ℝ) := by
  sorry

/--
**Erdős Problem 819** — Upper bound (Erdős–Freud [ErFr91]):

For every $\varepsilon > 0$, for sufficiently large $N$,
$f(N) \leq (1/2 + \varepsilon) N$.
-/
@[category research solved, AMS 5]
theorem erdos_819.variants.upper_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (↑(f N) : ℝ) ≤ (1 / 2 + ε) * (↑N : ℝ) := by
  sorry

end Erdos819
