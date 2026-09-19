/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 605

*References:*
- [erdosproblems.com/605](https://www.erdosproblems.com/605)
- [Er85] Erdős, P., *Problems and results in combinatorial geometry*. Discrete geometry and
  convexity (New York, 1982) (1985), 1-11.
- [EHP89] Erdős, Paul and Hickerson, Dean and Pach, János, *A problem of Leo Moser about repeated
  distances on the sphere*. Amer. Math. Monthly (1989), 569-575.
- [SwVa04] Swanepoel, Konrad J. and Valtr, Pavel, *The unit distance problem on spheres*. (2004),
  273-279.
-/

@[expose] public section

open Filter Metric Asymptotics

namespace Erdos605

/-- The Euclidean space $\mathbb{R}^3$. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/--
Is there some function $f(n)\to \infty$ as $n\to\infty$ such that there exist $n$ distinct points
on the surface of a two-dimensional sphere with at least $f(n)n$ many pairs of points whose
distances are the same?

This was solved by Erdős, Hickerson, and Pach [EHP89], who proved that one can take
$f(n) \gg \log^* n$ (where $\log^*$ is the iterated logarithm function). This was improved by
Swanepoel and Valtr [SwVa04] to $f(n) \gg \sqrt{\log n}$.

See also [90](https://www.erdosproblems.com/90).
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos605.lean#L457"]
theorem erdos_605 : answer(True) ↔ ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ ∀ n : ℕ,
    ∃ (P : Finset ℝ³) (c : ℝ³) (r d : ℝ), P.card = n ∧ (P : Set ℝ³) ⊆ sphere c r ∧
      0 < d ∧ f n * n ≤ distanceMultiplicity P d := by
  sorry

/--
For $D>1$ and $n\geq 2$, `u D n` is the maximum number of pairs of points at distance $1$ among
$n$ points on the sphere of radius $D$ in $\mathbb{R}^3$.
-/
noncomputable def u (D : ℝ) (n : ℕ) : ℕ :=
  sSup {m | ∃ P : Finset ℝ³,
    P.card = n ∧ (P : Set ℝ³) ⊆ sphere 0 D ∧ distanceMultiplicity P 1 = m}

/-- Erdős, Hickerson, and Pach [EHP89] proved that $u_{\sqrt{2}}(n)\asymp n^{4/3}$. -/
@[category research solved, AMS 52]
theorem erdos_605.variants.sqrt_two :
    (fun n : ℕ ↦ (u (√2) n : ℝ)) =Θ[atTop] fun n ↦ (n : ℝ) ^ (4 / 3 : ℝ) := by
  sorry

/--
Erdős, Hickerson, and Pach [EHP89] proved that $u_D(n)\gg n\log^*n$ for all $D>1$ and $n\geq 2$
(where $\log^*$ is the iterated logarithm function).
-/
@[category research solved, AMS 52]
theorem erdos_605.variants.log_star : ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 1 < D →
    ∀ n : ℕ, 2 ≤ n → c * n * Real.iteratedLog n ≤ u D n := by
  sorry

/-- Swanepoel and Valtr [SwVa04] proved that $u_D(n) \gg n\sqrt{\log n}$ for all $D>1$. -/
@[category research solved, AMS 52]
theorem erdos_605.variants.swanepoel_valtr : ∀ D : ℝ, 1 < D → ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n → c * n * √(Real.log n) ≤ u D n := by
  sorry

/-- The best upper bound for general $D$ is $u_D(n)\ll n^{4/3}$. -/
@[category research solved, AMS 52]
theorem erdos_605.variants.upper_bound : ∀ D : ℝ, 1 < D →
    (fun n : ℕ ↦ (u D n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (4 / 3 : ℝ) := by
  sorry

end Erdos605
