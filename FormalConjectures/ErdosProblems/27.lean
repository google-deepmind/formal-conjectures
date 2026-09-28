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
# Erdős Problem 27

*References:*
* [erdosproblems.com/27](https://www.erdosproblems.com/27)
* [Er95] Erdős, P., *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), p. 4.
* [FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C. and Yu, G., *Sieving by large
  integers and covering systems of congruences*. J. Amer. Math. Soc. (2007).
  [arXiv:math/0507374](https://arxiv.org/abs/math/0507374)
-/

@[expose] public section

namespace Erdos27

/-- The natural numbers that satisfy none of the congruences $x \equiv a(n) \pmod{n}$ for
$n \in S$. -/
def uncovered (S : Finset ℕ) (a : ℕ → ℕ) : Set ℕ :=
  {x | ∀ n ∈ S, ¬ x ≡ a n [MOD n]}

/-- A finite set of distinct moduli `S` with residues `a` is an $\varepsilon$-almost covering
system if the set of integers that satisfy none of the congruences has density at most
$\varepsilon$. -/
def IsAlmostCovering (ε : ℝ) (S : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ d ≤ ε, (uncovered S a).HasDensity d

@[category API, AMS 11]
theorem uncovered_empty (a : ℕ → ℕ) : uncovered ∅ a = Set.univ := by
  simp [uncovered]

/--
An $\varepsilon$-almost covering system is a set of congruences $a_i \pmod{n_i}$ for distinct
moduli $n_1 < \cdots < n_k$ such that the density of those integers which satisfy none of them
is at most $\varepsilon$.

Is there a constant $C > 1$ such that for every $\varepsilon > 0$ and $N \geq 1$ there is an
$\varepsilon$-almost covering system with $N \leq n_1 < \cdots < n_k \leq CN$?

The answer is no, as proved by Filaseta, Ford, Konyagin, Pomerance and Yu [FFKPY07].
-/
@[category research solved, AMS 11]
theorem erdos_27 : answer(False) ↔
    ∃ C > (1 : ℝ), ∀ ε > (0 : ℝ), ∀ N ≥ 1, ∃ (S : Finset ℕ) (a : ℕ → ℕ),
      (∀ n ∈ S, N ≤ n ∧ (n : ℝ) ≤ C * N) ∧ IsAlmostCovering ε S a := by
  sorry

/--
By a simple averaging argument, the moduli in $[m_1, m_2]$ have a choice of residues which forms
an $\varepsilon(m_1, m_2)$-almost covering system, where
$\varepsilon(m_1, m_2) = \prod_{m_1 \leq m \leq m_2} (1 - 1/m)$.
-/
@[category textbook, AMS 11]
theorem erdos_27.variants.averaging (m₁ m₂ : ℕ) (hm₁ : 1 ≤ m₁) :
    ∃ a : ℕ → ℕ, IsAlmostCovering (∏ m ∈ Finset.Icc m₁ m₂, (1 - 1 / (m : ℝ)))
      (Finset.Icc m₁ m₂) a := by
  sorry

end Erdos27
