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

/-!
# Ben Green's Open Problem 4

*Reference:* [Ben Green's Open Problem 4](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.4 Problem 4)
-/

namespace Green4
/--A set is product-free if for some * operation, there are no elements in the set x,y,z such that x*y=z
-/
def ProdFree {M : Type*} [Monoid M] (S : Set M) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x * y ≠ z

/-- What is the largest product-free set in the alternating group $A_n$?-/
@[category research open, AMS 20]
theorem green_4 (n : ℕ) :
    MaximalFor (ProdFree (M := alternatingGroup <| Fin n)) Set.ncard answer(sorry) := by
  sorry

/-- Defines a family of subsets of $A_n$ where each permutation π in a subset obeys π(x)∈I and ∀v∈I,
π(v)∉I for fixed x and I. It is easy to demonstrate that such a subset is product-free, because for
any a,b,c in such a set, (a*b) (x)=a(b(x))∉I but c(x)
-/
def extremalFamily {n : ℕ} (x : Fin n) (I : Set (Fin n)) : Set <| alternatingGroup <| Fin n :=
  {π | π.val x ∈ I ∧ Disjoint (I.image π) I}

/-- In the case of large n, the problem was solved in
[On the largest product-free subsets of the alternating groups](https://arxiv.org/pdf/2205.15191).
Specifically, this theorem formalizes the statement of theorem 1.1 in the mentioned paper
-/
@[category research solved, AMS 20]
theorem large_green_4: ∀ᶠn in Filter.atTop,
  ∀S, MaximalFor (ProdFree (M := alternatingGroup <| Fin n)) Set.ncard S →
  ∃x I, S = extremalFamily x I ∨ S = (extremalFamily x I).image (·⁻¹) := by
  sorry

end Green4
