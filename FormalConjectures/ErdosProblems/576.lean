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
# Erdős Problem 576

*References:*
- [erdosproblems.com/576](https://www.erdosproblems.com/576)
- [Er74c] Erdős, Paul, *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [ErSi70] Erdős, P. and Simonovits, M., *Some extremal problems in graph theory*.
  Combinatorial theory and its applications, I-III (1970), 377-390.
- [SuTo22] Sudakov, Benny and Tomon, István, *The extremal number of tight cycles*.
  Int. Math. Res. Not. IMRN (2022), 9663-9684.
- [JaSu22] Janzer, O. and Sudakov, B., *On the Turán number of the hypercube*.
  arXiv:2211.02015 (2024).
-/

@[expose] public section

namespace Erdos576

open Asymptotics Filter SimpleGraph

/--
Let $Q_k$ be the $k$-dimensional hypercube graph (so that $Q_k$ has $2^k$ vertices and
$k2^{k-1}$ edges). Determine the behaviour of $$\mathrm{ex}(n;Q_k).$$

The answer specifies the order of growth for each fixed dimension $k$.
-/
@[category research open, AMS 5]
theorem erdos_576 :
    (answer(sorry) : ℕ → ℕ → ℝ) ∈
      {f | ∀ k : ℕ,
        (fun n : ℕ => (extremalNumber n (hypercube k) : ℝ)) =Θ[atTop] f k} := by
  sorry

/--
In [Er74c], [Er81], and [Er93], Erdős asked whether
$\mathrm{ex}(n;Q_3)\asymp n^{8/5}$.
-/
@[category research open, AMS 5]
theorem erdos_576.variants.three_dimensional :
    answer(sorry) ↔
      (fun n : ℕ => (extremalNumber n (hypercube 3) : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (8 / 5 : ℝ)) := by
  sorry

/--
Erdős and Simonovits [ErSi70] proved that
$(1/2+o(1))n^{3/2}\leq\mathrm{ex}(n;Q_3)$.
-/
@[category research solved, AMS 5]
theorem erdos_576.variants.lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (1 / 2 - ε) * (n : ℝ) ^ (3 / 2 : ℝ) ≤
        (extremalNumber n (hypercube 3) : ℝ) := by
  sorry

/--
Erdős and Simonovits [ErSi70] proved that $\mathrm{ex}(n;Q_3)\ll n^{8/5}$.
-/
@[category research solved, AMS 5]
theorem erdos_576.variants.upper_bound :
    (fun n : ℕ => (extremalNumber n (hypercube 3) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (8 / 5 : ℝ)) := by
  sorry

/--
Erdős and Simonovits [ErSi70] also showed that if $Q_3'$ is the cube with one edge
missing then $\mathrm{ex}(n;Q_3')\asymp n^{3/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_576.variants.missing_edge :
    ∀ e ∈ (hypercube 3).edgeSet,
      (fun n : ℕ => (extremalNumber n ((hypercube 3).deleteEdges {e}) : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
Sudakov and Tomon [SuTo22] proved that $\mathrm{ex}(n;Q_k)=o(n^{2-1/k})$ for $k\geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_576.variants.sudakov_tomon (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ => (extremalNumber n (hypercube k) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 - 1 / (k : ℝ))) := by
  sorry

/--
Janzer and Sudakov [JaSu22] proved that
$\mathrm{ex}(n;Q_k)\ll_k n^{2-1/(k-1)+1/((k-1)2^{k-1})}$ for $k\geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_576.variants.janzer_sudakov (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ => (extremalNumber n (hypercube k) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^
        (2 - 1 / ((k : ℝ) - 1) + 1 / (((k : ℝ) - 1) * (2 : ℝ) ^ (k - 1)))) := by
  sorry

end Erdos576
