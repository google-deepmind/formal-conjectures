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
# Erdős Problem 710

*Reference:* [erdosproblems.com/710](https://www.erdosproblems.com/710)

Let $f(n)$ be minimal such that in $(n, n+f(n))$ there exist distinct integers
$a_1, \ldots, a_n$ such that $k \mid a_k$ for all $1 \le k \le n$. The problem asks
to obtain an asymptotic formula for $f(n)$.

A problem of Erdős and Pomerance [ErPo80], who proved
$$
(2/\sqrt{e} + o(1)) \cdot n \cdot (\log n / \log \log n)^{1/2} \le f(n)
\le (1.7398\ldots + o(1)) \cdot n \cdot (\log n)^{1/2}.
$$

Erdős [Er92c] offered a prize of 2000 rupees for an asymptotic formula.

See also [711]. See also OEIS [A390246](https://oeis.org/A390246).

[ErPo80] Erdős, P. and Pomerance, C., _Matching the natural numbers up to n with distinct multiples
in another interval_. Nederl. Akad. Wetensch. Proc. Ser. A 83 (= Indag. Math. 42) (1980), 147-161.

[Er92c] Erdős, P., _Some of my forgotten problems in number theory_. Hardy-Ramanujan J. 15 (1992),
34-50.
-/

open Nat

namespace Erdos710

/-- $f(n)$ for Erdős Problem 710: the minimal $f$ such that in the open interval
$(n, n+f)$ there exist $n$ distinct integers $a_1, \ldots, a_n$ with $k \mid a_k$ for all
$1 \le k \le n$. -/
noncomputable def erdos710F (n : ℕ) : ℕ :=
  sInf {f : ℕ | ∃ g : Fin n → ℕ,
    Function.Injective g ∧
    (∀ i : Fin n, n < g i) ∧
    (∀ i : Fin n, g i < n + f) ∧
    (∀ i : Fin n, (i.val + 1) ∣ g i)}

/--
Erdős Problem 710: Obtain an asymptotic formula for $f(n)$, defined as the minimal $f$ such
that in $(n, n+f)$ there exist distinct integers $a_1, \ldots, a_n$ with $k \mid a_k$ for all
$1 \le k \le n$. The answer is an unknown function $g$ such that $f(n) / g(n) \to 1$.
-/
@[category research open, AMS 11]
theorem erdos_710 :
    Filter.Tendsto (fun n : ℕ => (erdos710F n : ℝ) / (answer(sorry) : ℕ → ℝ) n)
      Filter.atTop (nhds 1) := by
  sorry

/--
Erdős Problem 710, known lower bound [ErPo80]:

For every $\varepsilon > 0$, there exists $N_0$ such that for all $n \ge N_0$,
$$
f(n) \ge (2/\sqrt{e} - \varepsilon) \cdot n \cdot (\log n / \log \log n)^{1/2}.
$$
-/
@[category research solved, AMS 11]
theorem erdos_710.variants.lower :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos710F n : ℝ) ≥
        (2 / (Real.exp 1) ^ ((1 : ℝ) / 2) - ε) * (n : ℝ) *
        (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Erdős Problem 710, known upper bound [ErPo80]:

For every $\varepsilon > 0$, there exists $N_0$ such that for all $n \ge N_0$,
$$
f(n) \le (1.7399 + \varepsilon) \cdot n \cdot (\log n)^{1/2}.
$$

The constant $1.7398\ldots$ comes from the original paper; we use $1.7399$ as
a rational upper bound on that constant.
-/
@[category research solved, AMS 11]
theorem erdos_710.variants.upper :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos710F n : ℝ) ≤
        (1.7399 + ε) * (n : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos710
