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
public import FormalConjectures.Wikipedia.Oppermann

/-!
# $a(n) = (\text{smallest prime} > n^2) - n^2$

The difference between the smallest prime strictly greater than $n^2$ and $n^2$.

*References:*
- [A053000](https://oeis.org/A053000)
- [November 2023 OEIS record](https://github.com/oeis/oeisdata/blob/5ba1d702dbbd1393fd5b8e9e135f3b1cb9954b6a/seq/A053/A053000.seq#L8)
-/

@[expose] public section

namespace OeisA53000

/-- $a(n) = (\text{smallest prime} > n^2) - n^2$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ n ^ 2 < p}) - n ^ 2

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := tsub_eq_of_eq_add <| IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := tsub_eq_of_eq_add <| IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := tsub_eq_of_eq_add <| IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := tsub_eq_of_eq_add <| IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := tsub_eq_of_eq_add <| IsLeast.csInf_eq <| by decide

/--
OEIS credits Jianglin Luo (September 22, 2023) with the conjecture that
$a(n) \le 1 + \phi(n)$ for $n > 0$. For $n \ge 2$ this implies the part of Oppermann's
conjecture asking for a prime between $n^2$ and $n(n+1)$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n ≤ 1 + n.totient := by
  sorry

/-- The totient bound implies the second part of Oppermann's conjecture. -/
@[category textbook, AMS 11]
theorem conjecture_implies_oppermann_part_ii (h : type_of% conjecture) :
    type_of% Oppermann.oppermann_conjecture.parts.ii := by
  intro n hn
  let p := sInf {p : ℕ | p.Prime ∧ n ^ 2 < p}
  have hp : p.Prime ∧ n ^ 2 < p := by
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (n ^ 2 + 1)
    exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ n ^ 2 < p}) ⟨q, hprime, hq⟩
  have hgap : p - n ^ 2 ≤ 1 + n.totient := h n (by omega)
  have hle : p ≤ n * (n + 1) := by
    rw [Nat.mul_succ, ← sq]
    have := Nat.totient_lt n hn
    omega
  refine ⟨p, Finset.mem_Ioo.2 ⟨hp.2, hle.lt_of_ne ?_⟩, hp.1⟩
  intro heq
  exact Nat.not_prime_mul (by omega : n ≠ 1) (by omega : n + 1 ≠ 1) (heq ▸ hp.1)

end OeisA53000
