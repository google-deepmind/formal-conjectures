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
# Erdős Problem 1110

*Reference:* [erdosproblems.com/1110](https://www.erdosproblems.com/1110)

Let $p > q \geq 2$ be two coprime integers. We call $n$ *representable* if it is the sum of
integers of the form $p^k q^l$, none of which divide each other.

If $\{p,q\} \neq \{2,3\}$ then what can be said about the density of non-representable numbers?
Are there infinitely many coprime non-representable numbers?

[ErLe96] Erdős, P. and Lewin, M., _$d$-complete sequences of integers_. Math. Comp. (1996),
837-840. Proved that there are finitely many non-representable numbers if and only if
$\{p,q\} = \{2,3\}$.

[YuCh22] Yu, W.-X. and Chen, Y.-G., _On a conjecture of Erdős and Lewin_. J. Number Theory
(2022), 763-778. Proved that the set of representable numbers has density zero for many cases,
and that there are infinitely many coprime non-representable numbers for most parameter choices.
Some cases remain open.

[YaZh25] Yang, Q.-H. and Zhao, L., _A conjecture of Yu and Chen related to the Erdős-Lewin
theorem_. Acta Arith. (2025), 277-286. Improved lower bounds on the growth rate.
-/

open Finset Classical

namespace Erdos1110

/-- A natural number $m$ is a $(p,q)$-power if $m = p^a \cdot q^b$ for some $a, b \geq 0$. -/
def IsPQPower (p q m : ℕ) : Prop :=
  ∃ a b : ℕ, m = p ^ a * q ^ b

/-- A natural number $n$ is $(p,q)$-representable if $n$ equals the sum of a nonempty finite set
of numbers of the form $p^a \cdot q^b$, where no element divides another. -/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧
    (∀ m ∈ S, IsPQPower p q m) ∧
    IsAntichain (· ∣ ·) (S : Set ℕ) ∧
    S.sum id = n

/--
Erdős Problem 1110 [ErLe96]:

For coprime integers $p > q \geq 2$ with $\{p,q\} \neq \{2,3\}$, there are infinitely many
non-representable numbers that are coprime to $p \cdot q$.

Since $p > q \geq 2$ and $p, q$ are coprime, the only excluded case is $p = 3, q = 2$.
-/
@[category research open, AMS 11]
theorem erdos_1110 : answer(sorry) ↔
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      ¬(p = 3 ∧ q = 2) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} := by
  sorry

/--
Erdős-Lewin theorem [ErLe96]: The set of non-representable numbers is finite if and only if
$\{p,q\} = \{2,3\}$ (i.e., $p = 3, q = 2$ given our convention $p > q$).
-/
@[category research solved, AMS 11]
theorem erdos_1110_erdos_lewin :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (Set.Finite {n : ℕ | ¬IsRepresentable p q n} ↔ (p = 3 ∧ q = 2)) := by
  sorry

end Erdos1110
