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
# Erdős Problem 921

*Reference:* [erdosproblems.com/921](https://www.erdosproblems.com/921)

Let $k \geq 4$ and let $f_k(n)$ be the largest $m$ such that there is a graph on $n$
vertices with chromatic number $k$ in which every odd cycle has length $> m$.
Is it true that $f_k(n) \asymp n^{1/(k-2)}$?

A question of Erdős and Gallai [Er69b]. Gallai proved that $f_4(n) \gg n^{1/2}$
and Erdős (unpublished) proved $f_4(n) \ll n^{1/2}$.

This was proved for all $k \geq 4$ by Kierstead, Szemerédi, and Trotter [KST84].

[Er69b] Erdős, P., *Problems and results in graph theory and combinatorics*, 1969.

[KST84] Kierstead, H., Szemerédi, E., and Trotter, W., *On coloring graphs with locally
few colors*, 1984.
-/

open SimpleGraph

namespace Erdos921

/-- The largest $m$ such that there exists a graph on $n$ vertices with chromatic
    number $k$ in which every odd cycle has length $> m$. -/
noncomputable def erdos921F (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.chromaticNumber = (k : ℕ∞) ∧
    ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → Odd p.length → m < p.length}

/--
Erdős Problem 921 [Er69b] [KST84]:

Is it true that $f_k(n) \asymp n^{1/(k-2)}$ for all $k \geq 4$?
This was proved by Kierstead, Szemerédi, and Trotter.
-/
@[category research solved, AMS 5]
theorem erdos_921 : answer(True) ↔
    ∀ k : ℕ, k ≥ 4 →
      (∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (erdos921F k n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2))) ∧
      (∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (erdos921F k n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2))) := by
  sorry

/--
Erdős Problem 921, lower bound [Er69b] [KST84]:

For every $k \geq 4$, there exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$f_k(n) \geq C \cdot n^{1/(k-2)}$.
-/
@[category research solved, AMS 5]
theorem erdos_921.variants.lower_bound (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos921F k n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2)) := by
  sorry

/--
Erdős Problem 921, upper bound [Er69b] [KST84]:

For every $k \geq 4$, there exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$f_k(n) \leq C \cdot n^{1/(k-2)}$.
-/
@[category research solved, AMS 5]
theorem erdos_921.variants.upper_bound (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos921F k n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2)) := by
  sorry

end Erdos921
