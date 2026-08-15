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

open Nat Group Fintype MulAut

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

universe u

/--
Conjecture 2: for n >= 2, if |Aut(G)| = a(n), then |G| = a(n)/p, where p = prime(n).
Moreover, G is unique up to isomorphism if p == 2 (mod 3).
We explicitly include Fintype (MulAut G) to satisfy the type checker's need for finiteness instance on card.
-/
theorem oeis_365179_conjecture_2 :
  ∀ (n : ℕ) (hn : 2 ≤ n),
    ∀ (G : Type u) [Group G] [Fintype G] [Fintype (MulAut G)],
      (Fintype.card (MulAut G) = A365179 n) →
      -- Part 1: Order relation, substituting p_n = Nat.nth Nat.Prime (n - 1)
      (Fintype.card G = A365179 n / Nat.nth Nat.Prime (n - 1)) ∧
      -- Part 2: Uniqueness up to isomorphism
      (Nat.nth Nat.Prime (n - 1) % 3 = 2 →
       ∀ (H : Type u) [Group H] [Fintype H] [Fintype (MulAut H)],
          Fintype.card (MulAut H) = A365179 n →
          Nonempty (G ≃* H)) :=
  by sorry
