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
# Diophantine $m$-tuples

A **Diophantine $m$-tuple** is a set of $m$ distinct positive integers
$\{a_1, \dots, a_m\}$ such that $a_i a_j + 1$ is a perfect square for every
$i \neq j$.

*References:*
- [Wikipedia - Diophantine tuple](https://en.wikipedia.org/wiki/Diophantine_tuple)
- https://www.ams.org/journals/notices/201607/rnoti-p772.pdf
- https://web.math.pmf.unizg.hr/~duje/quint.html
-/

namespace DiophantineTuple

variable {R : Type*} [Semiring R]


/--
A finite set `s` is a **Diophantine tuple** if each element is nonzero and the product
of any two distinct elements is one less than a perfect square.

We define this for all semirings and specialize to the integral and rational cases in this file;
these are the most common in the literature. Note that the cases of ℕ and ℕ+ are mathematically
equivalent.
-/
def IsDiophantineTuple (s : Finset R) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsSquare (x * y + 1)

abbrev IsIntegralDiophantineTuple (s : Finset ℕ) : Prop := IsDiophantineTuple (R := ℕ) s
abbrev IsRationalDiophantineTuple (s : Finset ℚ) : Prop := IsDiophantineTuple (R := ℚ) s

/--
The property of being a Diophantine tuple is closed under subsets.
-/
@[category textbook, AMS 11]
theorem isDiophantineTuple_of_subset (s t : Finset R) (h1 : IsDiophantineTuple t)
    (h2 : s ⊆ t) : IsDiophantineTuple s := by sorry

/-
Conjectures / theorems about existence of integral Diophantine m-tuples for various values of m
-/

/--
There exists a Diophantine 4-tuple; this example is due to Fermat.
-/
@[category test, AMS 11]
theorem fermat_4_tuple : IsIntegralDiophantineTuple {1, 3, 8, 120} := by
  norm_num [IsDiophantineTuple]

/--
The set of integral Diophantine 4-tuples.
-/
def integralDiophantine4Tuple : Set (Finset ℕ) :=
  { s | IsIntegralDiophantineTuple s ∧ s.card = 4 }

/--
There exist infinitely many integral Diophantine 4-tuples.

Proof: many parameterizations exist, e.g. {k, k + 2, 4k + 4, 16k³ + 48k² + 44k + 12}.
-/
@[category textbook, AMS 11]
example : integralDiophantine4Tuple.encard = ⊤ := by sorry

/--
The statement that there is no integral Diophantine 5-tuple.
-/
abbrev NoIntegralDiophantineFiveTuple := ¬∃ t, IsIntegralDiophantineTuple t ∧ t.card = 5

/--
The Diophantine 5-tuple theorem: there does not exist an integral Diophantine 5-tuple.

He, Togbé and Ziegler (https://arxiv.org/abs/1610.04020)
-/
@[category research solved, AMS 11]
theorem noIntegralDiophantineFiveTuple : NoIntegralDiophantineFiveTuple := by sorry

/-
Conjectures / theorems about extending integral Diophantine tuples
-/

/--
Given an integral Diophantine 3-tuple, there is a standard way to extend it to a 4-tuple by adjoining
the value of this function. This is d₊ in https://web.math.pmf.unizg.hr/~duje/quint.html.

Note that the terms in the sqrt (e.g. `a*b+1`) are perfect squares.
-/
def regularExtension (a b c : ℕ) : ℕ := a + b + c + 2*a*b*c + 2*Nat.sqrt ((a*b+1) * (a*c+1) * (b*c+1))

@[category test, AMS 11]
example : regularExtension 1 3 8 = 120 := by norm_num [regularExtension]

/--
The property that the Diophantine 3-tuple `{a, b, c}` extends to a 4-tuple `{a, b, c, d}`
with `d > max a b c` only via `regularExtension`.
-/
def HasUniqueExtension (a b c : ℕ) : Prop :=
  (IsIntegralDiophantineTuple { a, b, c }) ∧
  ∀ d : ℕ,
    (IsIntegralDiophantineTuple { a, b, c, d }) → max a (max b c) < d → d = regularExtension a b c

/--
The statement that every integral Diophantine triple of three distinct elements has a unique
extension by a larger element.
-/
abbrev HasUniqueExtensionOfForall :=
  ∀ a b c : ℕ, ({a, b, c} : Finset ℕ).card = 3 → IsIntegralDiophantineTuple {a, b, c} →
    HasUniqueExtension a b c

/--
The "strong Diophantine 5-tuple conjecture", so-called because it implies the Diophantine
5-tuple theorem (see `noIntegralDiophantineFiveTuple_of_hasUniqueExtensionOfForall`).
-/
@[category research open, AMS 11]
theorem hasUniqueExtension_of_forall : HasUniqueExtensionOfForall := by sorry

/--
If every integral Diophantine triple has a unique extension by a larger element, then there
is no integral Diophantine 5-tuple.

Proof: suppose a 5-tuple a < b < c < d₁ < d₂ exists; then d₁ = d₂ by unique extension.
-/
@[category textbook, AMS 11]
theorem noIntegralDiophantineFiveTuple_of_hasUniqueExtensionOfForall :
    HasUniqueExtensionOfForall → NoIntegralDiophantineFiveTuple := by sorry

/--
`HasUniqueExtension` is known to hold for certain triples, including (1, 3, 8): this is
essentially the Baker–Davenport theorem (1969), which states that 120 is the only integer `d`
such that `{1, 3, 8, d}` is a Diophantine tuple. Together with a finite check ruling out
`d < 8`, this shows that no integral Diophantine tuple properly extends {1, 3, 8, 120}.
-/
@[category research solved, AMS 11]
theorem hasUniqueExtension_of_1_3_8 : HasUniqueExtension 1 3 8 := by sorry

/-
Theorems and conjectures about the rational case
-/

/--
An example due to Euler which extends `fermat_4_tuple`, showing that
`hasUniqueExtension_of_1_3_8` requires integrality.
-/
@[category test, AMS 11]
example : IsRationalDiophantineTuple {1, 3, 8, 120, 777480/8288641} := by
  norm_num [IsDiophantineTuple]

/--
A known rational Diophantine 6-tuple.

Gibbs 1999
-/
@[category test, AMS 11]
theorem gibbs_6_tuple : IsRationalDiophantineTuple {11/192, 35/192, 155/27, 512/27, 1235/48, 180873/16} := by
  norm_num [IsDiophantineTuple]

/--
It is not known whether there exists a rational Diophantine 7-tuple.
-/
@[category research open, AMS 11]
theorem rational_7_tuple : answer(sorry) ↔ ∃ t, IsRationalDiophantineTuple t ∧ t.card = 7 := by
  sorry

end DiophantineTuple
