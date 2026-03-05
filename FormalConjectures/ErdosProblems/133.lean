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
# Erdős Problem 133

*Reference:* [erdosproblems.com/133](https://www.erdosproblems.com/133)

Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices
and diameter $2$ contains a vertex with degree $\geq f(n)$.

Does $f(n)/\sqrt{n}\to \infty$? This was asked by Erdős and Pach [ErPa90]. The answer is
**No**: $f(n) = \Theta(\sqrt{n})$.

Key results:
- Lower bound: $f(n) \geq \lfloor\sqrt{n-1}\rfloor$ from the Moore bound.
- [HaSe84] Hanson–Seyffarth: $f(n) \leq (\sqrt{2}+o(1))\sqrt{n}$.
- [FuSe94] Füredi–Seress: $f(n) \leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$.
- The precise asymptotic constant is unknown; Alon conjectures $f(n) \sim \sqrt{n}$.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos133

/-- A graph $G$ contains a triangle if there are three mutually adjacent vertices. -/
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A graph has diameter at most $2$ if every pair of distinct vertices is
either directly adjacent or has a common neighbor. -/
def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/-- $f(n)$ is the minimum $k$ such that every triangle-free graph on $n$ vertices
with diameter at most $2$ contains a vertex of degree at least $k$. Equivalently,
it is the minimum maximum-degree over all such graphs. When no such graph exists
(e.g. for $n = 1$) the infimum of the empty set is $0$. -/
noncomputable def erdos133_f (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬HasTriangle G → HasDiameterAtMostTwo G →
    ∃ v : Fin n, k ≤ G.degree v }

/--
Erdős Problem 133 (Main question, DISPROVED [HaSe84]):
The conjecture "$f(n)/\sqrt{n} \to \infty$" is false.
The Hanson–Seyffarth construction shows $f(n) = O(\sqrt{n})$, so the ratio
$f(n)/\sqrt{n}$ remains bounded.
-/
@[category research solved, AMS 5]
theorem erdos_133 : answer(False) ↔
    Tendsto (fun n : ℕ => (erdos133_f n : ℝ) / Real.sqrt n) atTop atTop := by
  sorry

/--
Erdős Problem 133 (Moore bound lower bound [ErPa90]):
$f(n) \geq \lfloor\sqrt{n-1}\rfloor$ for all $n \geq 1$.

Proof sketch: a graph with max degree $d$ and diameter $\leq 2$ has at most
$1 + d + d(d-1) = d^2+1$ vertices. Hence if $G$ is triangle-free on $n$
vertices with diameter $\leq 2$ and max degree $d$, then $n \leq d^2+1$,
giving $d \geq \sqrt{n-1}$.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Nat.sqrt (n - 1) ≤ erdos133_f n := by
  sorry

/--
Erdős Problem 133 (Hanson–Seyffarth upper bound [HaSe84]):
$f(n) \leq (\sqrt{2} + o(1))\sqrt{n}$.

For every $\varepsilon > 0$ and all sufficiently large $n$, there exists a
triangle-free graph on $n$ vertices with diameter $\leq 2$ and max degree
$\leq (\sqrt{2} + \varepsilon)\sqrt{n}$. The construction is a Cayley graph on
$\mathbb{Z}/n\mathbb{Z}$ with a symmetric complete sum-free generating set of
size $\sim \sqrt{n}$.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.hanson_seyffarth :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ (Real.sqrt 2 + ε) * Real.sqrt n := by
  sorry

/--
Erdős Problem 133 (Füredi–Seress improvement [FuSe94]):
$f(n) \leq (\frac{2}{\sqrt{3}} + o(1))\sqrt{n}$.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.furedi_seress :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt n := by
  sorry

/--
Erdős Problem 133 (DISPROVED [HaSe84]):
The ratio $f(n)/\sqrt{n}$ remains bounded, i.e., $f(n) = O(\sqrt{n})$.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.ratio_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ C * Real.sqrt n := by
  sorry

/--
Erdős Problem 133 (Open — precise asymptotics):
Both the lower bound $f(n) \geq (1 - o(1))\sqrt{n}$ and the upper bound
$f(n) \leq (\frac{2}{\sqrt{3}} + o(1))\sqrt{n}$ are known, but the precise
asymptotic constant is unknown. Alon conjectures $f(n) \sim \sqrt{n}$, i.e.,
$f(n)/\sqrt{n} \to 1$.
-/
@[category research open, AMS 5]
theorem erdos_133.variants.alon_conjecture :
    Tendsto (fun n : ℕ => (erdos133_f n : ℝ) / Real.sqrt n) atTop (nhds 1) := by
  sorry

end Erdos133
