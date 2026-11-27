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
# Valuations of the imaginary coordinate of a quadratic product

Peter Bala conjectured asymptotic growth laws for the valuations of the
coefficient of $\sqrt{-3}$ in $\prod_{k=1}^n(1+k\sqrt{-3})$.

*References:*
- [A363412](https://oeis.org/A363412)
-/

@[expose] public section

namespace OeisA363412

open Filter Topology

/-- The coefficient of $\sqrt{-3}$ in the product through $n$. -/
def a (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (⟨1, 1 + (k : ℤ)⟩ : Zsqrtd (-3))).im

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = -12 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = -140 := by decide

set_option linter.style.formal_proof_palomar false in
/--
The type 2 conjecture at $2$ predicts $v_2(a(n)) \sim n/2$.
The linked proof determines the valuation in each residue class modulo eight.
Codex formalized the proof at Dominic Dabish's request.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/formal-conjectures/blob/13fddc1c5327950e285065e0e289af92fed8f486/_certificates/oeis-quadratic-products/a363412-two-adic/A363412Limit.lean#L12-L17"]
theorem two_adic_valuation :
    Tendsto (fun n : ℕ ↦ 2 * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (𝓝 1) := by
  sorry

/--
At primes $p \equiv 1 \pmod{6}$, the type 2 conjecture predicts
$v_p(a(n)) \sim n/(p-1)$.
-/
@[category research open, AMS 11]
theorem split_prime_valuation {p : ℕ} (hp : p.Prime) (h : p % 6 = 1) :
    Tendsto (fun n : ℕ ↦ ((p : ℚ) - 1) * (padicValInt p (a n) : ℚ) / (n : ℚ))
      atTop (𝓝 1) := by
  sorry

end OeisA363412
