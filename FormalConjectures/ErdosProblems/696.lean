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
# Erdős Problem 696

*Reference:* [erdosproblems.com/696](https://www.erdosproblems.com/696)

Erdős asked whether $H(n)/h(n) \to \infty$ for almost all $n$, where $h(n)$ is the length of
the longest mod-chain of prime divisors of $n$ and $H(n)$ is the length of the longest mod-chain
of divisors of $n$.

[Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979), p. 81.
-/

open Classical Filter Finset

namespace Erdos696

/-- A list of natural numbers forms a mod-chain: it is strictly increasing
and consecutive elements satisfy $d_{i+1} \equiv 1 \pmod{d_i}$. -/
def IsModChain (l : List ℕ) : Prop :=
  List.IsChain (fun a b => a < b ∧ a ∣ (b - 1)) l

/-- $h(n)$: the largest $\ell$ such that there is a mod-chain of primes of length $\ell$
all dividing $n$. -/
noncomputable def hPrime (n : ℕ) : ℕ :=
  sSup {k | ∃ l : List ℕ, l.length = k ∧ IsModChain l ∧ ∀ p ∈ l, Nat.Prime p ∧ p ∣ n}

/-- $H(n)$: the largest $u$ such that there is a mod-chain of divisors of length $u$
all dividing $n$. -/
noncomputable def hDivisor (n : ℕ) : ℕ :=
  sSup {k | ∃ l : List ℕ, l.length = k ∧ IsModChain l ∧ ∀ d ∈ l, d ∣ n}

/-- Count of integers $m \in \{1, \ldots, N\}$ satisfying predicate $P$. -/
noncomputable def countSat (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => P (n + 1))).card

/--
Erdős Problem 696 [Er79e, p. 81]:

Is it true that $H(n)/h(n) \to \infty$ for almost all $n$?

Formulated as: for every $M > 0$, the natural density of
$\{n : H(n) \geq M \cdot h(n)\}$ is $1$.
-/
@[category research open, AMS 11]
theorem erdos_696 : answer(sorry) ↔
    ∀ M : ℝ, M > 0 →
    Tendsto
      (fun N : ℕ =>
        (countSat (fun n => (hDivisor n : ℝ) ≥ M * (hPrime n : ℝ)) (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
  sorry

end Erdos696
