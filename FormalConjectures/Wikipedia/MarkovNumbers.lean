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

A *Markov triple* is a triple $(x, y, z)$ of positive integers with $x^2 + y^2 + z^2 = 3xyz$.
A *Markov number* is an integer that appears in some Markov triple.
For example, $(1, 2, 5)$ is a Markov triple, since $1 + 4 + 25 = 30 = 3 \cdot 1 \cdot 2 \cdot 5$.

Frobenius conjectured in 1913 that every Markov number $c$ is the largest entry of exactly one
Markov triple $(a, b, c)$ with $a \le b \le c$. This *unicity conjecture* is still open.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Markov_number)
 - [OEIS A002559](https://oeis.org/A002559)
 - G. Frobenius, *Über die Markoffschen Zahlen*, S. B. Preuss. Akad. Wiss. (1913), 458–487.
 - M. Aigner, *Markov's Theorem and 100 Years of the Uniqueness Conjecture*, Springer (2013).
-/

@[expose] public section

namespace MarkovNumbers

/-- A *Markov triple* consists of three positive integers $x, y, z$ such that
$x \leq y \leq z$ and we have the Markov equality $x^2 + y^2 + z^2 = 3xyz$. -/
@[ext] structure MarkovTriple where
  x : ℕ
  y : ℕ
  z : ℕ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  x_le_y : x ≤ y
  y_le_z : y ≤ z
  markov_eq : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- A positive integer $c$ is a *Markov number* if it appears in some Markov triple. -/
def IsMarkovNumber (c : ℕ) : Prop :=
  ∃ t : MarkovTriple, t.x = c ∨ t.y = c ∨ t.z = c

@[category test, AMS 11]
theorem markovTriple_one_two_five :
  ∃ t : MarkovTriple, t.x = 1 ∧ t.y = 2 ∧ t.z = 5 := by
    use ⟨1, 2, 5, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

@[category test, AMS 11]
theorem not_markovTriple_one_two_three :
    ¬ ∃ t : MarkovTriple, t.x = 1 ∧ t.y = 2 ∧ t.z = 3 := by
  rintro ⟨t, hx, hy, hz⟩
  have h := t.markov_eq
  rw [hx, hy, hz] at h
  linarith

/-- The *unicity conjecture*, posed by Frobenius, says that for every positive integer $c$,
if $c$ is a Markov number, then there is exactly one Markov triple whose largest entry is $c$. -/
@[category research open, AMS 11]
theorem markov_unicity_conjecture :
    ∀ c, IsMarkovNumber c → ∃! t : MarkovTriple, t.z = c := by
  sorry

end MarkovNumbers
