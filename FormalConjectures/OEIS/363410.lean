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
# Imaginary coordinate of a quadratic product

The sequence consists of the coefficients of $\sqrt{-2}$ in
$\prod_{k=1}^n (1+k\sqrt{-2})$.

*References:*
- [A363410](https://oeis.org/A363410)
-/

@[expose] public section

namespace OeisA363410

open Filter Topology

/-- The coefficient of $\sqrt{-2}$ in the product through $n$. -/
def a (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (⟨1, 1 + (k : ℤ)⟩ : Zsqrtd (-2))).im

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = -6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = -90 := by decide

/--
The type 1 conjecture states that “every prime p divides some term of this sequence.”
A nonzero witness excludes the initial term $a(0)=0$.
Codex formalized the triangular-number proof at Dominic Dabish's request.
-/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/OeisSolutions.lean#L38-L41"]
theorem prime_divides_some_term {p : ℕ} (hp : p.Prime) :
    ∃ n : ℕ, a n ≠ 0 ∧ (p : ℤ) ∣ a n := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The type 3 conjecture describes “oscillatory behavior” at $2$ and at primes congruent to $5$ or
$7$ modulo $8$. Here every tail contains a term coprime to $p$ and nonzero terms divisible by
arbitrarily high powers of $p$. The source explicitly leaves oscillation undefined.
Codex formalized the norm argument at Dominic Dabish's request.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/OeisSolutions.lean#L45-L50"]
theorem oscillating_primes {p : ℕ} (hp : p.Prime) :
    ((∀ e N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ 0 ∧ (p : ℤ) ^ e ∣ a n) ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ (p : ℤ) ∣ a n)) ↔
        p = 2 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  sorry

/--
The type 2 conjectures predict the asymptotic $v_p(a(n)) \sim n/(p-1)$
for primes $p$ congruent to $1$ or $3$ modulo $8$.
-/
@[category research open, AMS 11]
theorem split_prime_valuation {p : ℕ} (hp : p.Prime) (h : p % 8 = 1 ∨ p % 8 = 3) :
    Tendsto (fun n : ℕ ↦ ((p : ℚ) - 1) * (padicValInt p (a n) : ℚ) / (n : ℚ))
      atTop (𝓝 1) := by
  sorry

end OeisA363410
