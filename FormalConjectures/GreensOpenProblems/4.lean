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
import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 4

*Reference:* [Ben Green's Open Problem 4](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.4 Problem 4)
-/

namespace Green4
def A (n : ℕ) := alternatingGroup (Fin n)

def ProdFree {n : ℕ} (S : Set (Equiv.Perm (Fin n))) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x * y ≠ z

def LargestProdFree (n : ℕ) (S : Set (Equiv.Perm (Fin n))) : Prop := (∀x ∈ S , x ∈ A n) ∧
  ProdFree S ∧ (∀S' : Set (Equiv.Perm (Fin n)), (∀x ∈ S',x ∈ A n) → ProdFree S' →
    S'.ncard ≤ S.ncard)

/-- What is the largest product-free set in the alternating group A_n?-/
@[category research open,AMS 20]
theorem green_4 (n : ℕ) : LargestProdFree n answer(sorry) := sorry

def extremalFamily {n : ℕ} (x : Fin n) (I : Set (Fin n)) : Set (Equiv.Perm (Fin n)) :=
  {π | π ∈ A n ∧ π x ∈ I ∧ Disjoint (I.image π) I}

/-In the case of large n, the problem was solved in
[On the largest product-free subsets of the alternating groups](https://arxiv.org/pdf/2205.15191)
-/
@[category research solved, AMS 20]
theorem large_green_4: ∃N : ℕ, ∀n > N, ∀S, LargestProdFree n S → ∃x I, S = extremalFamily x I ∨
  S = (extremalFamily x I).image Equiv.symm := sorry
end Green4
