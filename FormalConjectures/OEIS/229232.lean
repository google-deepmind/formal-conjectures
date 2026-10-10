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
# Undirected circular permutations with adjacent products minus one all prime

Number of undirected circular permutations $\pi(1), \dots, \pi(n)$ of $1, \dots, n$ with the $n$
numbers $\pi(1)\pi(2)-1, \pi(2)\pi(3)-1, \dots, \pi(n-1)\pi(n)-1, \pi(n)\pi(1)-1$ all prime.

*References:*
- [A229232](https://oeis.org/A229232)
-/

namespace OeisA229232

/-- Number of undirected circular permutations $\pi(1), \dots, \pi(n)$ of $1, \dots, n$ with the
$n$ numbers $\pi(1)\pi(2)-1, \pi(2)\pi(3)-1, \dots, \pi(n-1)\pi(n)-1, \pi(n)\pi(1)-1$ all prime. -/
def a (n : ℕ) : ℕ :=
  if n < 3 then 0
  else
    let l_n : List ℕ := (List.range n).map (· + 1)
    let all_perms : List (List ℕ) := l_n.permutations
    let good_perms := all_perms.filter fun p =>
      (p.zip (p.rotate (n - 1))).all fun pair => decide ((pair.1 * pair.2 - 1).Prime)
    good_perms.length / (2 * n)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by native_decide

@[category test, AMS 11]
theorem a_6 : a 6 = 2 := by native_decide

@[category test, AMS 11]
theorem a_7 : a 7 = 1 := by native_decide

@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by native_decide

/--
Conjecture: $a(n) > 0$ for all $n > 5$ with $n$ not equal to $13$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 5) (hne : n ≠ 13) : a n > 0 := by
  sorry

/--
Conjecture: For any integer $n > 1$, there is a permutation $\pi(1), \dots, \pi(n)$ of $1, \dots, n$
such that the $n$ numbers $2\pi(1)\pi(2)-1, \dots, 2\pi(n-1)\pi(n)-1, 2\pi(n)\pi(1)-1$ are
all prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 1) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n,
      (2 * ((π i).val + 1) *
        ((π ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩).val + 1) - 1).Prime := by
  sorry

/--
Conjecture: For any positive integer $n$ not equal to $4$, there is a permutation
$\pi(1), \dots, \pi(n)$ of $1, \dots, n$ such that the $n$ numbers
$2\pi(1)\pi(2)+1, \dots, 2\pi(n-1)\pi(n)+1, 2\pi(n)\pi(1)+1$ are all prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : n > 0) (hne : n ≠ 4) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n,
      (2 * ((π i).val + 1) * ((π ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩).val + 1) + 1).Prime := by
  sorry

/--
Conjecture: Let $F$ be a finite field with $q > 7$ elements. Then, there is a circular
permutation $a_1, \dots, a_{q-1}$ of the $q-1$ nonzero elements of $F$ such that all the $q-1$
elements $a_1 a_2 - 1, a_2 a_3 - 1, \dots, a_{q-2} a_{q-1} - 1, a_{q-1} a_1 - 1$ are
primitive elements of the field $F$ (i.e., generators of the multiplicative group
$F \setminus \{0\}$).
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11 12]
theorem conjecture4 (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F > 7) :
    let m := Fintype.card F - 1
    ∃ a : Fin m ≃ Fˣ,
      ∀ i : Fin m, IsPrimitiveRoot
        ((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F) - 1) m := by
  sorry

/--
Conjecture: Let $F$ be a finite field with $q > 7$ elements. There is a circular permutation
$b_1, \dots, b_{q-1}$ of the $q-1$ nonzero elements of $F$ such that all the $q-1$ elements
$b_1 b_2 + 1, b_2 b_3 + 1, \dots, b_{q-2} b_{q-1} + 1, b_{q-1} b_1 + 1$ are primitive elements
of the field $F$ (i.e., generators of the multiplicative group $F \setminus \{0\}$).
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11 12]
theorem conjecture5 (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F > 7) :
    let m := Fintype.card F - 1
    ∃ b : Fin m ≃ Fˣ,
      ∀ i : Fin m, IsPrimitiveRoot
        ((b i : F) * (b ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F) + 1) m := by
  sorry

end OeisA229232
