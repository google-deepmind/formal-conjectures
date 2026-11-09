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
# Markov numbers

A *Markov triple* is a triple $(x, y, z)$ of positive natural numbers with $x^2 + y^2 + z^2 = 3xyz$.
A *Markov number* is a natural number that appears in some Markov triple.
For example, $(1, 2, 5)$ is a Markov triple, since $1 + 4 + 25 = 30 = 3 \cdot 1 \cdot 2 \cdot 5$.

Frobenius conjectured in 1913 that every Markov number $c$ is the largest entry of exactly one
Markov triple $(a, b, c)$ with $a \le b \le c$. This *unicity conjecture* is still open.

New Markov triples can be obtained from old ones: if $(x, y, z)$ is a Markov triple, then so is
$(x, y, 3xy - z)$. Together with reordering the entries, this operation produces every Markov triple
starting from $(1, 1, 1)$. The unicity conjecture has been verified by computer for all
$c \le 10^{500000}$, but no proof is known.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Markov_number)
 - [OEIS A002559](https://oeis.org/A002559)
 - G. Frobenius, *Über die Markoffschen Zahlen*, S. B. Preuss. Akad. Wiss. (1913), 458–487.
 - M. Aigner, *Markov's Theorem and 100 Years of the Uniqueness Conjecture*, Springer (2013).
 - H. Tan, Y. Zhang, *A Computational Verification of the Markov Uniqueness Conjecture for
   $z \le 10^{500000}$*, [arXiv:2611.01007](https://arxiv.org/abs/2611.01007) (2026).
-/

@[expose] public section

namespace MarkovNumbers

/-- A *Markov triple* consists of three positive natural numbers $x, y, z$ such that
$x \leq y \leq z$ and we have the Markov equality $x^2 + y^2 + z^2 = 3xyz$. -/
def IsMarkovTriple (x y z : ℕ) : Prop :=
  0 < x ∧ x ≤ y ∧ y ≤ z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- A positive natural number $c$ is a *Markov number* if it appears in some Markov triple. -/
def IsMarkovNumber (c : ℕ) : Prop :=
  ∃ a b : ℕ, IsMarkovTriple a b c ∨ IsMarkovTriple a c b ∨ IsMarkovTriple c a b

@[category test, AMS 11]
theorem isMarkovTriple_one_two_five : IsMarkovTriple 1 2 5 := by
  simp [IsMarkovTriple]

@[category test, AMS 11]
theorem not_isMarkovTriple_one_two_three : ¬IsMarkovTriple 1 2 3 := by
  simp [IsMarkovTriple]

/-- The *unicity conjecture*, posed by Frobenius, says that for every positive natural number $c$,
if $c$ is a Markov number, then there is exactly one Markov triple whose largest entry is $c$. -/
@[category research open, AMS 11]
theorem markov_unicity_conjecture :
    ∀ c, IsMarkovNumber c → ∃! q : ℕ × ℕ, IsMarkovTriple q.1 q.2 c := by
  sorry

end MarkovNumbers
