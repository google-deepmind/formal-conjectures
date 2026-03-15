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
import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Erdős Problem 877

*Reference:* [erdosproblems.com/877](https://www.erdosproblems.com/877)

Let $f_m(n)$ count the number of maximal sum-free subsets $A \subseteq \{1, \ldots, n\}$ — that is,
$A$ contains no three elements $a, b, c$ with $a = b + c$, and $A$ is maximal with this
property (no element of $\{1, \ldots, n\} \setminus A$ can be added while preserving sum-freeness).

Is it true that $f_m(n) = o(2^{n/2})$?

Cameron and Erdős [CaEr90] proved that $f_m(n) > 2^{n/4}$. Łuczak and Schoen [LuSc01] proved
that there exists $c < 1/2$ with $f_m(n) < 2^{cn}$, resolving the conjecture.
Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved $f_m(n) = 2^{(1/4+o(1))n}$,
later refined [BLST18] to $f_m(n) = (C_n + o(1)) \cdot 2^{n/4}$.

[CaEr90] Cameron, P.J. and Erdős, P.

[Er98] Erdős, P., _Some of my favourite problems which recently have been solved_,
Challenges for the 21st century (Singapore, 2000), 2001.

[LuSc01] Łuczak, T. and Schoen, T., _On the number of maximal sum-free sets_,
Proc. Amer. Math. Soc. (2001), 2205–2207.

[BLST15] Balogh, J., Liu, H., Sharifzadeh, M., and Treglown, A., _The number of maximal
sum-free subsets of integers_, Proc. Amer. Math. Soc. (2015), 4713–4721.

[BLST18] Balogh, J., Liu, H., Sharifzadeh, M., and Treglown, A., _Sharp bound on the number
of maximal sum-free subsets of integers_, J. Eur. Math. Soc. (JEMS) (2018), 1885–1911.
-/

open scoped Classical Pointwise
open Finset

namespace Erdos877

/-- A subset $A$ of $\{1, \ldots, n\}$ is a *maximal sum-free subset* if it is sum-free
and no element of $\{1, \ldots, n\} \setminus A$ can be added while preserving
sum-freeness. -/
def IsMaximalSumFree (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧
  IsSumFree (A : Set ℕ) ∧
  ∀ x ∈ Finset.Icc 1 n, x ∉ A → ¬ IsSumFree (↑(insert x A) : Set ℕ)

/-- The number of maximal sum-free subsets of $\{1, \ldots, n\}$. -/
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => IsMaximalSumFree A n)).card

/--
Erdős Problem 877 [CaEr90][Er98]:

Let $f_m(n)$ count the number of maximal sum-free subsets of $\{1, \ldots, n\}$. Then
$$f_m(n) = o(2^{n/2}).$$

That is, for every $\varepsilon > 0$, for all sufficiently large $n$,
$$f_m(n) \leq \varepsilon \cdot 2^{n/2}.$$

Proved by Łuczak and Schoen [LuSc01], with the sharp asymptotics
$f_m(n) = 2^{(1/4+o(1))n}$ established by Balogh–Liu–Sharifzadeh–Treglown [BLST15].
-/
@[category research solved, AMS 5]
theorem erdos_877 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maximalSumFreeCount n : ℝ) ≤ ε * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

end Erdos877
