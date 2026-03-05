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
# Erdős Problem 456

*Reference:* [erdosproblems.com/456](https://www.erdosproblems.com/456)

Let $p_n$ be the smallest prime $\equiv 1 \pmod{n}$ and let $m_n$ be the
smallest positive integer such that $n \mid \phi(m_n)$.

1. Is it true that $m_n < p_n$ for almost all $n$?
2. Does $p_n / m_n \to \infty$ for almost all $n$?
3. Are there infinitely many primes $p$ such that $p - 1$ is the only $n$
   for which $m_n = p$?

Linnik's theorem implies that $p_n \leq n^{O(1)}$. It is trivial that
$m_n \leq p_n$ always. If $n = q - 1$ for some prime $q$ then $m_n = p_n$.

[Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset Filter Classical

open scoped Topology

namespace Erdos456

/-- The smallest prime congruent to $1$ modulo $n$. -/
noncomputable def smallestPrimeCong1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD n]}

/-- The smallest positive integer $m$ such that $n \mid \phi(m)$. -/
noncomputable def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ Nat.totient m}

/--
Erdős Problem 456, Part 1 [Er79e, p.80]:

Is it true that $m_n < p_n$ for almost all $n$?

Formalized as: the density of $\{n : m_n \geq p_n\}$ is $0$, i.e., the
proportion of $n \leq x$ for which $p_n \leq m_n$ tends to $0$ as $x \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_456 :
    answer(sorry) ↔
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        smallestPrimeCong1 n ≤ smallestTotientDiv n)).card : ℝ) / (x : ℝ))
      atTop (nhds 0) := by
  sorry

/--
Erdős Problem 456, Part 2 [Er79e, p.80]:

Does $p_n / m_n \to \infty$ for almost all $n$?

Formalized as: for every $C > 0$, the density of $\{n : p_n \leq C \cdot m_n\}$
is $0$.
-/
@[category research open, AMS 11]
theorem erdos_456.variants.ratio_diverges :
    answer(sorry) ↔
    ∀ C : ℝ, 0 < C →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          (smallestPrimeCong1 n : ℝ) ≤ C * (smallestTotientDiv n : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) := by
  sorry

/--
Erdős Problem 456, Part 3 [ErGr80, p.91]:

Are there infinitely many primes $p$ such that $p - 1$ is the only $n$ for
which $m_n = p$?
-/
@[category research open, AMS 11]
theorem erdos_456.variants.unique_preimage :
    answer(sorry) ↔
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      smallestTotientDiv (p - 1) = p ∧
      ∀ n : ℕ, smallestTotientDiv n = p → n = p - 1} := by
  sorry

end Erdos456
