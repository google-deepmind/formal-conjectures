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
# Sum of $d \cdot \tau(d)$ over proper divisors $d$ of $n$

The sequence $a(n)$ is the sum of $d \cdot \tau(d)$ over all proper divisors $d < n$ of $n$,
where $\tau(d)$ is the number of divisors of $d$:
$$a(n) = \sum_{d \mid n, d < n} d \cdot \tau(d)$$

*References:*
- [A245211](https://oeis.org/A245211)
- [Su26] Mar Allen P. Sugui,
  [General Parity Obstructions, $\Omega(n) \le 4$ Fixed-Point Exclusions, and Proper-Divisor Moments for OEIS A245211 in Lean 4](https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/docs/oeis-a245211/oeis-a245211.pdf),
  2026.
-/

@[expose] public section

namespace OeisA245211

open Finset
open scoped ArithmeticFunction.Omega

/-- Sum over all proper divisors $d$ of $n$ of $d \cdot \tau(d)$, where $\tau(d)$ is the
number of divisors of $d$. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d * d.divisors.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide

@[category test, AMS 11]
theorem a_21 : a 21 = 21 := by
  decide

/--
"Formula: a(p) = 1 for prime p." - _Jaroslav Krizek_, Jul 23 2014
-/
@[category research solved, AMS 11]
theorem a_prime {p : ℕ} (hp : p.Prime) : a p = 1 := by
  simp [a, hp.properDivisors]

/--
Conjecture: $21$ is the only positive integer $n$ such that $a(n) = n$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n = n ↔ n = 21 := by
  sorry

/--
No even positive integer $n$ satisfies $a(n) = n$: for $n = 2m$ with $m \ge 2$, the proper
divisors $1$ and $m$ contribute at least $1 + 2m = n + 1$ to $a(n)$.
-/
@[category research solved, AMS 11]
theorem conjecture.variants.even (n : ℕ) (hn : 0 < n) (heven : Even n) : a n ≠ n := by
  rcases heven with ⟨m, rfl⟩
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
  · decide
  · have hsub : ({1, m} : Finset ℕ) ⊆ (m + m).properDivisors := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩
      · rcases mem_singleton.mp hx with rfl
        exact Nat.mem_properDivisors.mpr ⟨⟨2, by ring⟩, by omega⟩
    have hle := sum_le_sum_of_subset (f := fun d ↦ d * d.divisors.card) hsub
    rw [sum_pair (by omega), Nat.divisors_one, card_singleton, one_mul] at hle
    have hcard : 2 ≤ m.divisors.card := by
      have hdiv : ({1, m} : Finset ℕ) ⊆ m.divisors := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩
        · rcases mem_singleton.mp hx with rfl
          exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
      have hle_card := card_le_card hdiv
      rw [card_pair (by omega)] at hle_card
      exact hle_card
    have hmul : 2 * m ≤ m * m.divisors.card := by nlinarith
    change a (m + m) ≠ m + m
    unfold a
    omega

set_option linter.style.formal_proof_palomar false in
/--
Bounded verification of `conjecture` for $1 \le n \le 150$: $n = 21$ is the unique
positive integer $n \le 150$ satisfying $a(n) = n$. See [Su26, Theorem 7.2].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/oeis-a245211/OeisA245211/TableCerts.lean#L123"]
theorem conjecture.variants.le_150 (n : ℕ) (hn1 : 1 ≤ n) (hn150 : n ≤ 150) :
    a n = n ↔ n = 21 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
No prime power $p^k$ ($k \ge 1$) satisfies $a(p^k) = p^k$, since $a(p^k) \equiv 1 \pmod p$.
See [Su26, Theorem 4.2].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/oeis-a245211/OeisA245211/Families.lean#L303"]
theorem conjecture.variants.prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    a (p ^ k) ≠ p ^ k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Among all multiples of $3$, $n = 21$ is the unique fixed point of $a(n)$.
See [Su26, Theorem 4.4].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/oeis-a245211/OeisA245211/Families.lean#L458"]
theorem conjecture.variants.three_dvd (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    a n = n ↔ n = 21 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
General parity obstruction: if $n > 0$ is a non-square fixed point ($a(n) = n$ and
$\tau(n)$ is even) and $p^e \parallel n$ for an odd prime $p$ and exponent $e \ge 1$, then
$e \equiv 0 \text{ or } 1 \pmod 4$. See [Su26, Theorem 5.3].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/oeis-a245211/OeisA245211/Parity.lean#L550"]
theorem conjecture.variants.parity_obstruction {n p e : ℕ} (hn : 0 < n) (ha : a n = n)
    (htau : Even n.divisors.card) (hp : p.Prime) (hp_odd : Odd p)
    (he : 1 ≤ e) (hdvd : p ^ e ∣ n) (hndvd : ¬ p ^ (e + 1) ∣ n) :
    e % 4 = 0 ∨ e % 4 = 1 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Unconditional confirmation of `conjecture` for all positive integers $n$ with at most four
prime factors counted with multiplicity ($\Omega(n) \le 4$): $a(n) = n \iff n = 21$.
See [Su26, Theorem 6.3].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/oeis-a245211/OeisA245211/OmegaFour.lean#L945"]
theorem conjecture.variants.omega_le_four (n : ℕ) (hn : 0 < n) (hΩ : Ω n ≤ 4) :
    a n = n ↔ n = 21 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Unconditional confirmation of `conjecture` for all positive integers $n$ with at most five
prime factors counted with multiplicity ($\Omega(n) \le 5$): $a(n) = n \iff n = 21$.
Proved by combining the $\Omega(n) = 5$ non-squarefree / $p \ge 17$ reduction [Su26, Theorem 6.4]
with the 5-prime growth bound ($p \ge 73$) and Cunningham prime-factor forced closure across
$17 \le p \le 71$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/f6d8623a8f4086e074aa8caf3c27ff1a5cd30075/lean/oeis-a245211/OeisA245211/OmegaFive.lean#L336"]
theorem conjecture.variants.omega_le_five (n : ℕ) (hn : 0 < n) (hΩ : Ω n ≤ 5) :
    a n = n ↔ n = 21 := by
  sorry

end OeisA245211
