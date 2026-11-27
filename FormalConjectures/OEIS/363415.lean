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
# Real part of a quadratic product

The sequence consists of the real parts of $\prod_{k=1}^n (1+k\sqrt{-5})$.

*References:*
- [A363415](https://oeis.org/A363415)
-/

@[expose] public section

namespace OeisA363415

open Filter Topology

/-- The real part of the product through $n$. -/
def a (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (⟨1, 1 + (k : ℤ)⟩ : Zsqrtd (-5))).re

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = -9 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = -54 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 426 := by decide

set_option linter.style.formal_proof_palomar false in
/--
The source conjectures that the “set of type 1 primes begins” with a list that jumps from
$137$ to $157$. The corrected prefix through $197$ includes $139$ as well.
Codex formalized the modular computation and the proof for all indices at Dominic Dabish's request.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/OeisSolutions.lean#L30-L35"]
theorem type_one_prime_prefix {p : ℕ} (hp : p.Prime) (hb : p ≤ 197) :
    (∀ n, ¬ (p : ℤ) ∣ a n) ↔
      p ∈ ([5, 11, 13, 31, 53, 79, 97, 113, 137, 139, 157, 179, 193, 197] : List ℕ) := by
  sorry

/--
The conjecture for odd split primes predicts the asymptotic $v_p(a(n)) \sim n/(p-1)$
for primes $p$ congruent to $1$, $3$, $7$ or $9$ modulo $20$.
-/
@[category research open, AMS 11]
theorem split_prime_valuation {p : ℕ} (hp : p.Prime)
    (h : p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9) :
    Tendsto (fun n : ℕ ↦ ((p : ℚ) - 1) * (padicValInt p (a n) : ℚ) / (n : ℚ))
      atTop (𝓝 1) := by
  sorry

end OeisA363415
