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

open Nat

/--
A365179: $a(1) = 2$; for $n \ge 2$, $a(n) = p^6$ if $p \equiv 2 \pmod 3$, $a(n) = p^7$ if $p = 3$ or $p \equiv 1 \pmod 3$, where $p = \text{prime}(n)$.
-/
noncomputable def A365179 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then
      p ^ 6
    else
      p ^ 7

/-- The $n$-th prime number, where $\text{prime}(1)=2$. -/
noncomputable def prime_of_index (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The property that a natural number $m$ is the order of the automorphism group
of a finite, non-trivial group, and $m$ is a positive power of $p$. -/
def is_possible_aut_order_power (p m : ℕ) : Prop :=
  (∃ (k : ℕ) (hk : 0 < k), m = p ^ k) ∧
  (∃ (G : Type) (inst_group : Group G) (inst_fintype : Fintype G) (inst_aut_fintype : Fintype (MulAut G)),
    1 < Fintype.card G ∧ Fintype.card (MulAut G) = m)

/--
Conjecture 1: a(n) is the smallest nontrivial power of p such that there exists a finite nontrivial group whose automorphism group is of order a(n).
-/
theorem A365179_conjecture_1 (n : ℕ) (hn : 2 ≤ n) :
  let p := prime_of_index n;
  is_possible_aut_order_power p (A365179 n) ∧
  ∀ m' : ℕ, (is_possible_aut_order_power p m') → (A365179 n) ≤ m' :=
  by sorry
