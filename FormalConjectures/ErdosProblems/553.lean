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
# Erdős Problem 553

*References:*
- [erdosproblems.com/553](https://www.erdosproblems.com/553)
- [ErSo80] Erdős, P. and Sós, Vera T., Problems and results on Ramsey-Turán type theorems
  (preliminary report). Proceedings of the West Coast Conference on Combinatorics, Graph Theory
  and Computing (Humboldt State Univ., Arcata, Calif., 1979) (1980), 17-23.
- [AlRo05] Alon, Noga and Rödl, Vojtěch, Sharp bounds for some multicolor Ramsey numbers.
  Combinatorica (2005), 125--141.
- [Sh83] Shearer J., A note on the independence number of triangle-free graphs. Discrete Math.
  (1983), 83-87.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos553

/-- `R(3,3,n)`: the smallest `m` such that every `3`-colouring of the edges of `K_m` contains a
monochromatic triangle in one of the first two colours or a monochromatic `K_n` in the third
colour. -/
noncomputable def ramsey33 (n : ℕ) : ℕ :=
  sInf {m | ∀ C : TopEdgeLabeling (Fin m) (Fin 3),
    ¬ (C.labelGraph 0).CliqueFree 3 ∨ ¬ (C.labelGraph 1).CliqueFree 3 ∨
      ¬ (C.labelGraph 2).CliqueFree n}

/--
Let $R(3,3,n)$ denote the smallest integer $m$ such that if we $3$-colour the edges of $K_m$ then
there is either a monochromatic triangle in one of the first two colours or a monochromatic $K_n$
in the third colour. Define $R(3,n)$ similarly but with two colours. Show that
$$\frac{R(3,3,n)}{R(3,n)}\to \infty$$
as $n\to \infty$.

A problem of Erdős and Sós. This was solved by Alon and Rödl [AlRo05], who in fact show that
$R(3,3,n)\asymp n^3(\log n)^{O(1)}$ (recalling that Shearer [Sh83] showed
$R(3,n) \ll n^2/\log n$).

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos553.lean#L256"]
theorem erdos_553 : Tendsto (fun n : ℕ ↦ (ramsey33 n : ℝ) / classicalRamsey 3 n) atTop atTop := by
  sorry

/--
Alon and Rödl [AlRo05] show that $R(3,3,n)\asymp n^3(\log n)^{O(1)}$: there are constants
$c, C, K > 0$ such that $c\, n^3 (\log n)^{-K} \leq R(3,3,n) \leq C\, n^3 (\log n)^{K}$ for all
large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_553.variants.alon_rodl : ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    c * n ^ 3 * Real.log n ^ (-K) ≤ ramsey33 n ∧ (ramsey33 n : ℝ) ≤ C * n ^ 3 * Real.log n ^ K := by
  sorry

end Erdos553
