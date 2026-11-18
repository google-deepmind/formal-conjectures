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
# Automorphism group orders of certain graphs

$a(1) = 2$, and for $n \ge 2$, $a(n) = p^6$ if $p \equiv 2 \pmod 3$, and $p^7$ if $p = 3$ or $p
\equiv 1 \pmod 3$,
where $p = p_n$ is the $n$-th prime.

*References:*
- [A365179](https://oeis.org/A365179)
-/

open Nat Group Fintype MulAut

namespace OeisA365179

/--
$a(1) = 2$; for $n \ge 2$, $a(n) = p^6$ if $p \equiv 2 \pmod 3$, and $p^7$ if $p = 3$ or $p
\equiv 1 \pmod 3$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then
      p ^ 6
    else
      p ^ 7

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2187 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 15625 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 823543 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_5 : a 5 = 1771561 := by unfold a; norm_num

/-- The $n$-th prime number, where $\text{prime}(1)=2$. -/
noncomputable def prime_of_index (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The property that a natural number $m$ is the order of the automorphism group
of a finite, non-trivial group, and $m$ is a positive power of $p$. -/
def is_possible_aut_order_power (p m : ℕ) : Prop :=
  (∃ (k : ℕ) (_ : 0 < k), m = p ^ k) ∧
  (∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : Fintype (MulAut G)),
    1 < Fintype.card G ∧ Fintype.card (MulAut G) = m)

/--
$a(n)$ is the smallest nontrivial power of $p$ such that there exists a finite
nontrivial group whose automorphism group is of order $a(n)$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 2 ≤ n) :
    let p := prime_of_index n
    is_possible_aut_order_power p (a n) ∧
    ∀ m' : ℕ, is_possible_aut_order_power p m' → a n ≤ m' := by
  sorry

universe u

/--
For $n \ge 2$, if $|\operatorname{Aut}(G)| = a(n)$, then $|G| = a(n)/p$, where $p =
\operatorname{prime}(n)$.
Moreover, $G$ is unique up to isomorphism if $p \equiv 2 \pmod 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
    ∀ (n : ℕ) (_ : 2 ≤ n),
      ∀ (G : Type u) [Group G] [Fintype G] [Fintype (MulAut G)],
        (Fintype.card (MulAut G) = a n) →
        (Fintype.card G = a n / Nat.nth Nat.Prime (n - 1)) ∧
        (Nat.nth Nat.Prime (n - 1) % 3 = 2 →
         ∀ (H : Type u) [Group H] [Fintype H] [Fintype (MulAut H)],
            Fintype.card (MulAut H) = a n →
            Nonempty (G ≃* H)) := by
  sorry

end OeisA365179
