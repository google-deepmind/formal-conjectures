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
# Erdős Problem 468

*Reference:* [erdosproblems.com/468](https://www.erdosproblems.com/468)

For any $n$ let $D_n$ be the set of partial sums $d_1, d_1+d_2, d_1+d_2+d_3, \ldots$
where $1 < d_1 < d_2 < \cdots$ are the divisors of $n$.

The problem asks two questions:
1. What is the size of $D_n \setminus \bigcup_{m < n} D_m$? (Not formalized — too imprecise.)
2. If $f(N)$ is the minimal $n$ such that $N \in D_n$, is it true that $f(N) = o(N)$?
   Perhaps just for almost all $N$?

The formalization captures question 2 in both a strong form ($f(N) = o(N)$ for all $N$)
and a weak form ($f(N) = o(N)$ for almost all $N$, in the natural density sense).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset Filter

namespace Erdos468

/-- Prefix sums of a list with accumulator.
Returns $[\mathrm{acc}+a_1, \mathrm{acc}+a_1+a_2, \ldots]$. -/
def prefixSums : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: as, acc => (acc + a) :: prefixSums as (acc + a)

/-- $D_n$: the set of partial sums of the divisors of $n$ that are greater than $1$,
taken in increasing order. -/
def D (n : ℕ) : Finset ℕ :=
  (prefixSums ((n.divisors.filter (1 < ·)).sort (· ≤ ·)) 0).toFinset

/-- $f(N)$: the minimal $n$ such that $N \in D_n$. -/
noncomputable def f (N : ℕ) : ℕ :=
  sInf {n : ℕ | N ∈ D n}

/--
Erdős Problem 468, strong form [ErGr80]:

If $f(N)$ is the minimal $n$ such that $N \in D_n$, then $f(N) = o(N)$.
-/
@[category research open, AMS 11]
theorem erdos_468 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (f N : ℝ) < ε * (N : ℝ) := by
  sorry

/--
Erdős Problem 468, weak form [ErGr80]:

$f(N) = o(N)$ for almost all $N$. Formalized as: for any $\varepsilon > 0$, the density of
$\{N \le x : f(N) \ge \varepsilon \cdot N\}$ tends to $0$ as $x \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_468.variants.weak : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun N =>
          (f N : ℝ) ≥ ε * (N : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) := by
  sorry

end Erdos468
