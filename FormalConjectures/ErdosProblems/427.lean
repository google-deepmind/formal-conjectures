/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 427

*Reference:* [erdosproblems.com/427](https://www.erdosproblems.com/427)
-/

@[expose] public section

namespace Erdos427

/--
The predicate that for every $n$ and $d$, there exists $k$ such that
$$
  d \mid p_{n + 1} + \cdots + p_{n + k},
$$
where $p_r$ denotes the $r$th prime?
-/
def erdos427 : Prop := ∀ (n d : ℕ),
    -- Need to allow `n = 0` since we're counting primes from `0` rather than `1`
    -- `d` needs to be `≠ 0` since the sum is never `0`!
    d ≠ 0 → ∃ k, k ≠ 0 ∧
    d ∣ ∑ i ∈ Finset.Ico n (n + k), i.nth Nat.Prime

/--
The statement of Shiu's theorem:
for any $k \geq 1$ and $(a, q) = 1$ there exist infinitely many $k$-tuples of consecutive primes
$p_m, \dots, p_{m + k - 1}$ all of which are congruent to $a$ modulo $q$.

[Sh00] Shiu, D. K. L., _Strings of congruent primes_. J. London Math. Soc. (2) (2000), 359-373.
-/
def ShiuTheorem : Prop := ∀ (k a q : ℕ), 1 ≤ k → 1 ≤ q → a.gcd q = 1 →
    { m : ℕ | ∀ p ∈ (Finset.Ico m (m + k)).image (Nat.nth Nat.Prime), p ≡ a [MOD q]}.Infinite


/--
**Shiu's theorem**: for any $k \geq 1$ and $(a, q) = 1$ there exist infinitely many $k$-tuples of consecutive primes
$p_m, \dots, p_{m + k - 1}$ all of which are congruent to $a$ modulo $q$.

This is stated ahead of `erdos_427` because the formal proof linked there assumes it, and the
`assuming` clause must name a declaration that already exists.

[Sh00] Shiu, D. K. L., _Strings of congruent primes_. J. London Math. Soc. (2) (2000), 359-373.
-/
@[category research solved, AMS 11]
theorem erdos_427.variants.shiu : ShiuTheorem := by
  sorry


/--
**Erdős Problem 427**: is it true that, for every $n$ and $d$, there exists $k$ such that
$$
  d \mid p_{n + 1} + \cdots + p_{n + k},
$$
where $p_r$ denotes the $r$th prime?
-/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/Jayyhk/erdos-lean/blob/main/problems/427/Erdos427.lean"]
theorem erdos_427 : erdos427 := by
  sorry


/--
Cedric Pilatte has observed that a positive solution to Erdős Problem 427 follows from Shiu's theorem.
-/
@[category research solved, AMS 11]
theorem erdos_427.variants.of_shiu (H : ShiuTheorem) : erdos427 := by
  intro n d hd
  obtain ⟨m, hm, hnm⟩ := (H d 1 d (by omega) (by omega) (by simp)).exists_gt n
  have hp : ∀ i < d, (m + i).nth Nat.Prime ≡ 1 [MOD d] := fun i hi =>
    hm _ (Finset.mem_image.2 ⟨m + i, Finset.mem_Ico.2 ⟨by omega, by omega⟩, rfl⟩)
  set S := ∑ i ∈ Finset.Ico n m, i.nth Nat.Prime
  set j := d - S % d with hj
  have hS := Nat.mod_lt S (by omega : 0 < d)
  refine ⟨m - n + j, by omega, ?_⟩
  have hsplit : ∑ i ∈ Finset.Ico n (n + (m - n + j)), i.nth Nat.Prime =
      S + ∑ i ∈ Finset.range j, (m + i).nth Nat.Prime := by
    rw [show n + (m - n + j) = m + j by omega,
      ← Finset.sum_Ico_consecutive _ hnm.le (by omega : m ≤ m + j)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show m + j - m = j by omega]
  have hmod : ∑ i ∈ Finset.range j, (m + i).nth Nat.Prime ≡ j [MOD d] := by
    calc ∑ i ∈ Finset.range j, (m + i).nth Nat.Prime
        ≡ ∑ i ∈ Finset.range j, 1 [MOD d] :=
          Nat.ModEq.sum fun i hi => hp i (by have := Finset.mem_range.1 hi; omega)
      _ = j := by simp
  rw [hsplit, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
  rcases Nat.eq_zero_or_pos (S % d) with h | h
  · rw [hj, h, Nat.sub_zero, Nat.mod_self]
    simp
  · rw [Nat.mod_eq_of_lt (by omega : j < d), hj, show S % d + (d - S % d) = d by omega,
      Nat.mod_self]

end Erdos427
