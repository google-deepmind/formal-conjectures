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
open Finset

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)


theorem a_one : a 1 = 1 := by
  simp_all [a]

theorem a_two : a 2 = 1 := by
  delta a
  norm_num [((congr_arg _) ↑ _).trans ( (3).nth_count ↑_)]

theorem a_three : a 3 = 2 := by
  delta a
  norm_num [show (2).nth _ = 5 ∧ (3).nth _ = 7 from ⟨Nat.nth_count Nat.prime_five, Nat.nth_count (by decide : (7).Prime)⟩]

theorem a_four : a 4 = 12 := by
  norm_num [a ·]
  exact (13).nth_count (by decide: (13).Prime) ▸ rfl

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by sorry
