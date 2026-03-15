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
# Erdős Problem 535

*Reference:* [erdosproblems.com/535](https://www.erdosproblems.com/535)

Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of
$\{1, \ldots, N\}$ such that no subset of size $r$ has the same pairwise
greatest common divisor between all elements. Estimate $f_r(N)$.

Erdős [Er64] proved that $f_r(N) \leq N^{3/4+o(1)}$, and Abbott and Hanson
[AbHa70] improved this exponent to $1/2$. Erdős [Er64] proved the lower bound
$f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$, and conjectured this
should also be an upper bound.

This problem is intimately connected with the sunflower problem [20].
See also Problem 536, the dual problem about triples with equal pairwise LCM.

[Er64] Erdős, P., *On a problem in elementary number theory and a
combinatorial problem*. Math. Comp. (1964), 644--646.

[Er69] Erdős, P., *On some applications of graph theory to number theoretic
problems*. Publ. Ramanujan Inst. 1 (1969), 131--136.

[Er70] Erdős, P. (1970)

[Er73] Erdős, P., *Problems and results on combinatorial number theory*.
A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State
Univ., Fort Collins, Colo., 1971) (1973), 117--138.

[AbHa70] Abbott, H.L. and Hanson, D., *An extremal problem in number theory*.
Bull. London Math. Soc. (1970), 324--326.
-/

open Finset Real

namespace Erdos535

/-- A set $A$ of natural numbers is $r$-GCD-uniform-free if no $r$-element
subset has all pairwise GCDs equal. That is, there is no $r$-element subset
$S \subseteq A$ and value $d$ such that $\gcd(a, b) = d$ for all distinct
$a, b \in S$. -/
def IsGCDUniformFree (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = r →
    ¬∃ d : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b = d

/--
**Erdős Problem 535** (Upper bound conjecture):

There exists a constant $c > 0$ and $N_0$ such that for all $N \geq N_0$, every
$3$-GCD-uniform-free subset of $\{1, \ldots, N\}$ has size at most
$N^{c / \log\log N}$.

Erdős [Er64] conjectured this specifically for $r = 3$, matching the proved
lower bound.

See [Er64].
-/
@[category research open, AMS 5 11]
theorem erdos_535 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N → IsGCDUniformFree A 3 →
        (A.card : ℝ) ≤ (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) := by
  sorry

/--
**Erdős Problem 535** (Lower bound, proved by Erdős [Er64] for $r = 3$):

There exists a constant $c > 0$ and $N_0$ such that for all $N \geq N_0$,
there exists a $3$-GCD-uniform-free subset of $\{1, \ldots, N\}$ of size at
least $N^{c / \log\log N}$.

See [Er64].
-/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.lower_bound :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsGCDUniformFree A 3 ∧
        (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) ≤ (A.card : ℝ) := by
  sorry

/--
**Erdős Problem 535** (Erdős's original upper bound [Er64]):

There exists $N_0$ such that for all $r \geq 3$ and $N \geq N_0$, every
$r$-GCD-uniform-free subset of $\{1, \ldots, N\}$ has size at most
$N^{3/4 + o(1)}$. More precisely, for every $\varepsilon > 0$ there exists
$N_0$ such that $f_r(N) \leq N^{3/4 + \varepsilon}$ for all $N \geq N_0$.

See [Er64].
-/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.erdos_upper_bound (r : ℕ) (hr : 3 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N → IsGCDUniformFree A r →
        (A.card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
  sorry

/--
**Erdős Problem 535** (Abbott-Hanson upper bound [AbHa70]):

For all $r \geq 3$, for every $\varepsilon > 0$ there exists $N_0$ such that
for all $N \geq N_0$, every $r$-GCD-uniform-free subset of $\{1, \ldots, N\}$
has size at most $N^{1/2 + \varepsilon}$. This improves Erdős's original
$3/4$ exponent.

See [AbHa70].
-/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.abbott_hanson_upper_bound (r : ℕ) (hr : 3 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N → IsGCDUniformFree A r →
        (A.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  sorry

end Erdos535
