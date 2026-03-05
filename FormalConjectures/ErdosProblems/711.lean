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
# Erdős Problem 711

*Reference:* [erdosproblems.com/711](https://www.erdosproblems.com/711)

A problem of Erdős and Pomerance on the function $f(n,m)$, the minimal $f$ such that
in the open interval $(m, m+f)$ there exist distinct integers $a_1, \ldots, a_n$ with
$k \mid a_k$ for all $1 \leq k \leq n$.

[ErPo80] Erdős, P. and Pomerance, C., 1980.

[vD26] van Doorn, 2026.
-/

open Nat

namespace Erdos711

/-- $f(n,m)$ for Erdős Problem 711: the minimal $f$ such that in the open interval
$(m, m+f)$ there exist $n$ distinct integers $a_1, \ldots, a_n$ with $k \mid a_k$ for all
$1 \leq k \leq n$. When $m = n$ this coincides with the function in Problem 710. -/
noncomputable def f (n m : ℕ) : ℕ :=
  sInf {f : ℕ | ∃ g : Fin n → ℕ,
    Function.Injective g ∧
    (∀ i : Fin n, m < g i) ∧
    (∀ i : Fin n, g i < m + f) ∧
    (∀ i : Fin n, (i.val + 1) ∣ g i)}

/--
Erdős Problem 711, Part 1 [ErPo80]:

Prove that $\max_m f(n,m) \leq n^{1+o(1)}$.

Formulated as: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$
and all $m$,
$$f(n,m) \leq n^{1+\varepsilon}.$$

Erdős and Pomerance proved the weaker bound $\max_m f(n,m) \ll n^{3/2}$.
-/
@[category research open, AMS 11]
theorem erdos_711 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ m : ℕ,
        (f n m : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  sorry

/--
Erdős Problem 711, Part 2 [ErPo80]:

Prove that $\max_m (f(n,m) - f(n,n)) \to \infty$.

Formulated as: for every $C$, there exists $N_0$ such that for all $n \geq N_0$,
there exists $m$ with $f(n,m) \geq f(n,n) + C$.

van Doorn [vD26] proved that for all large $n$ there exists $m$ with
$f(n,m) - f(n,n) \gg (\log n / \log \log n) \cdot n$.
-/
@[category research solved, AMS 11]
theorem erdos_711.variants.divergence :
    ∀ C : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ m : ℕ, f n m ≥ f n n + C := by
  sorry

end Erdos711
