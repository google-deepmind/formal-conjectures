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
# Erdős Problem 781

*Reference:* [erdosproblems.com/781](https://www.erdosproblems.com/781)

Let $f(k)$ be the minimal $n$ such that any 2-colouring of $\{1,\ldots,n\}$ contains
a monochromatic $k$-term descending wave: a sequence $x_1 < \cdots < x_k$ such that,
for $1 < j < k$, $x_j \geq (x_{j+1} + x_{j-1}) / 2$.

A problem of Brown, Erdős, and Freedman [BEF90], who proved
$k^2 - k + 1 \leq f(k) \leq (k^3 - 4k + 9) / 3$.
They conjectured $f(k) = k^2 - k + 1$ for all $k$.
Disproved by Alon and Spencer [AlSp89] who proved $f(k) \gg k^3$.

[BEF90] Brown, T. C., Erdős, P., and Freedman, A. R., _Quasi-progressions and descending
waves_. J. Combin. Theory Ser. A **53** (1990), 81-95.

[AlSp89] Alon, N. and Spencer, J., _Ascending waves_. J. Combin. Theory Ser. A **52**
(1989), 275-287.
-/

namespace Erdos781

/-- A $k$-term descending wave in $\{0, \ldots, n-1\}$: a strictly increasing sequence
$x : \mathrm{Fin}\; k \to \mathrm{Fin}\; n$ such that for every interior index $j$
($0 < j$ and $j+1 < k$), $2 x(j) \geq x(j+1) + x(j-1)$.

Equivalently, the gaps $x(j+1) - x(j)$ are non-increasing. -/
def IsDescendingWave (k n : ℕ) (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
  ∀ (j : Fin k) (_ : 0 < j.val) (hj : j.val + 1 < k),
    2 * (x j).val ≥ (x ⟨j.val + 1, hj⟩).val + (x ⟨j.val - 1, by omega⟩).val

/-- A 2-colouring of $\{0, \ldots, n-1\}$ contains a monochromatic $k$-term
descending wave. -/
def HasMonochromaticDescendingWave (k n : ℕ) (c : Fin n → Bool) : Prop :=
  ∃ x : Fin k → Fin n, IsDescendingWave k n x ∧
    ∃ a : Bool, ∀ i : Fin k, c (x i) = a

/-- $f(k)$: the minimal $n$ such that every 2-colouring of $\{0, \ldots, n-1\}$ contains
a monochromatic $k$-term descending wave. -/
noncomputable def descendingWaveNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ c : Fin n → Bool, HasMonochromaticDescendingWave k n c}

/--
Alon–Spencer [AlSp89]: $f(k) \gg k^3$.

There exists $C > 0$ such that for all sufficiently large $k$,
$f(k) \geq C \cdot k^3$. This disproves the conjecture that $f(k) = k^2 - k + 1$.
-/
@[category research solved, AMS 5]
theorem erdos_781 :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (descendingWaveNumber k : ℝ) ≥ C * (k : ℝ) ^ 3 := by
  sorry

/--
Erdős Problem 781, lower bound [BEF90]:
For all $k \geq 1$, $f(k) \geq k^2 - k + 1$.
-/
@[category research solved, AMS 5]
theorem erdos_781.variants.bef_lower_bound (k : ℕ) (hk : k ≥ 1) :
    descendingWaveNumber k ≥ k ^ 2 - k + 1 := by
  sorry

/--
Erdős Problem 781, upper bound [BEF90]:
For all $k \geq 2$, $f(k) \leq (k^3 - 4k + 9) / 3$.
-/
@[category research solved, AMS 5]
theorem erdos_781.variants.bef_upper_bound (k : ℕ) (hk : k ≥ 2) :
    descendingWaveNumber k ≤ (k ^ 3 - 4 * k + 9) / 3 := by
  sorry

end Erdos781
