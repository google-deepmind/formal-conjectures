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

import FormalConjecturesUtil

/-!
# Numbers $n$ such that the perfect deficiency of $n$ is $\le 10$.

A108864 lists the numbers $n$ whose *perfect deficiency* is at most $10$. The perfect
deficiency is [A109883](https://oeis.org/A109883), a greedy divisor-subtraction quantity. It is
not the deviation $|\sigma_1(n) - 2n|$ from perfection: for example $24$ is a term of A108864
and has perfect deficiency $0$, while $|\sigma_1(24) - 2 \cdot 24| = 12$.

*References:*
- [A108864](https://oeis.org/A108864)
- [A109883](https://oeis.org/A109883)
-/

namespace OeisA108864

open Nat Finset

/--
The *perfect deficiency* of $n$, [A109883](https://oeis.org/A109883): "start subtracting from
$n$ its divisors beginning from $1$ until one reaches a number smaller than the last divisor
subtracted or reaches the last nontrivial divisor $< n$".

`(List.range (n + 1)).filter (· ∣ n)` is the list of divisors of $n$ in increasing order (see
`mem_divisorList_iff`). The fold subtracts each of them from the running remainder unless the
remainder has already fallen below it. That single guard captures both stopping rules of the
quoted description. Once the remainder is smaller than one divisor it is smaller than every
later divisor, so the fold is constant from that point on; and for $n > 1$ the divisor $n$
itself is never subtracted, because the remainder is already $< n$ once $1$ has been
subtracted. For $n = 1$ the only divisor $1$ is subtracted, giving `perfectDeficiency 1 = 0`,
which is the value A109883 records.

`perfectDeficiency 0 = 0`. The sequence predicate below excludes $0$ explicitly, so this junk
value is never used.

The divisors are listed by filtering a range rather than by sorting `Nat.divisors`, because
the fold has to see them in increasing order and the filtered range reduces in the kernel,
which the `test` theorems below rely on.
-/
def perfectDeficiency (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (· ∣ n)).foldl (fun r d => if r < d then r else r - d) n

/-- The list folded over by `perfectDeficiency` is exactly the set of divisors of `n`. -/
@[category API, AMS 11]
theorem mem_divisorList_iff {n d : ℕ} (hn : 0 < n) :
    d ∈ (List.range (n + 1)).filter (· ∣ n) ↔ d ∈ n.divisors := by
  simp only [List.mem_filter, List.mem_range, Nat.lt_succ_iff, decide_eq_true_eq,
    Nat.mem_divisors]
  exact ⟨fun h => ⟨h.2, hn.ne'⟩, fun h => ⟨Nat.le_of_dvd hn h.1, h.1⟩⟩

/--
The condition for a number $n$ to be in the sequence.
It satisfies $0 < n$ and its perfect deficiency is $\le 10$.
-/
def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

instance : DecidablePred A := by
  unfold A
  infer_instance

/--
The primary defining sequence `a`.
`a n` is the `n`-th number (0-indexed) such that its perfect deficiency is $\le 10$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-- The first ten terms of [A109883](https://oeis.org/A109883), the perfect deficiency. -/
@[category test, AMS 11]
theorem perfectDeficiency_values :
    (List.range' 1 10).map perfectDeficiency = [0, 1, 2, 1, 4, 0, 6, 1, 5, 2] := by
  decide

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h2 : A 2 := by decide
  have hcnt : Nat.count A 2 = 1 := by decide
  have := Nat.nth_count (p := A) h2
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h3 : A 3 := by decide
  have hcnt : Nat.count A 3 = 2 := by decide
  have := Nat.nth_count (p := A) h3
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 3 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  have h5 : A 5 := by decide
  have hcnt : Nat.count A 5 = 4 := by decide
  have := Nat.nth_count (p := A) h5
  rwa [hcnt] at this

/--
$24$ is the twentieth term of A108864. Subtracting $1, 2, 3, 4, 6, 8$ from $24$ leaves $0$, so
the perfect deficiency of $24$ is $0$.

This term separates the perfect deficiency from the deviation from perfection:
$\sigma_1(24) = 60$, so $|\sigma_1(24) - 2 \cdot 24| = 12 > 10$.
-/
@[category test, AMS 11]
theorem a_19 : a 19 = 24 := by
  have h24 : A 24 := by decide
  have hcnt : Nat.count A 24 = 19 := by decide
  have := Nat.nth_count (p := A) h24
  rwa [hcnt] at this

/--
Is 1155 the last odd number in this sequence?
(1155 is the 59th term starting from 1, corresponding to `a 58 = 1155`).
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ n > 58, Even (a n) := by
  sorry

end OeisA108864
