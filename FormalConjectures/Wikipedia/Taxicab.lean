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
# Taxicab numbers

A *taxicab number* for natural numbers $k, m, n$ is the smallest number $x$ that can be expressed as a sum of $m$ positive $k$-th powers in at least $n$ distinct ways. The most famous taxicab number is
$ 1729 = 1³ + 12³ = 9³ + 10³, $
also known as the Hardy–Ramanujan number.

However, a taxicab number is not known for $k=5$, $m=2$, and any $n ≥ 2$:
No positive integer is known that can be written as the sum of two 5th powers in more than one way, and it is not known whether such a number exists.

In particular, it is not known whether there exists a taxicab number for $k=5$, $m=2$, and $n=2$.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Taxicab_number)
 - [Generalized taxicab number](https://en.wikipedia.org/wiki/Generalized_taxicab_number)
 - [OEIS taxicab cubes](https://oeis.org/A001235)
 - [OEIS taxicab 4th powers](https://oeis.org/A018786)
 - [OEIS taxicab conjecture](https://oeis.org/A088703)
-/

namespace Taxicab

/-- $x$ is a candidate for being a taxicab number for $k, m, n$ if there exists a (finite) set of at least $n$ distinct, pairwise disjoint, non-empty, non-zero lists of length $m$, such that the sum of the $k$-th powers of the elements of each list is $x$. The disjointness condition ensures that the representations do not share any common terms.
-/
def IsTaxicabFor' (k m n x : ℕ) : Prop :=
  ∃ (S : Finset (List ℕ)),
  S.card ≥ n ∧
  ∀ L ∈ S, ∀ M ∈ S, L ≠ M → List.Disjoint L M ∧
  (∀ L ∈  S, L.length = m ∧ L ≠ [] ∧ 0 ∉ L ∧ (L.map (· ^ k)).sum = x)

/-- $1729$ is a possible taxicab number for $k=3, m=2, n=2$.
-/
@[category test, AMS 11]
theorem taxicab_1729 : IsTaxicabFor' 3 2 2 1729 := by
  use {{1, 12}, {9, 10}}
  simp [List.Disjoint];
  simp +decide

/-- $x$ is a taxicab number if it is the smallest number that can be expressed as a sum of $m$ positive $k$-th powers in at least $n$ distinct ways.
-/
def IsTaxicabFor (k m n : ℕ) (x : ℕ) : Prop :=
  IsLeast { x : ℕ | IsTaxicabFor' k m n x } x

@[category test, AMS 11]
theorem taxicab_4' : IsTaxicabFor' 1 2 2 4 := by
  use {[1, 3], [2, 2]};
  simp [List.Disjoint];

/-- Using Aristotle (Harmonic) we get a compact proof that 4 is the taxicab number for $k=1, m=2, n=2$. -/
@[category test, AMS 11]
theorem taxicab_4 : IsTaxicabFor 1 2 2 4 := by
  constructor;
  · exact taxicab_4';
  · rintro x ⟨ S, hS₁, hS₂ ⟩;
    obtain ⟨ s, hs, t, ht, hst ⟩ := Finset.one_lt_card.mp hS₁;
    have := hS₂ s hs t ht hst;
    rcases this with ⟨ h₁, h₂ ⟩ ;
    specialize h₂ s hs;
    rcases s with ( _ | ⟨ a, _ | ⟨ b, _ | s ⟩ ⟩ ) <;> simp_all +arith +decide;
    rcases t with ( _ | ⟨ c, _ | ⟨ d, _ | t ⟩ ⟩ ) <;> simp_all +arith +decide;
    · grind;
    · have := hS₂ _ ht _ hs; simp_all +decide ;
      grind;
    · have := hS₂ _ hs _ ht; simp_all +decide [ List.Disjoint ] ;
      have := this.2 _ hs; have := this.2.2; simp_all +arith +decide;
      grind;
    · have := hS₂ _ hs _ ht; simp_all +decide [ List.Disjoint ] ;
      grind +ring

/-- Taxicab number for $k=5$, $m=2$, and $n=2$ is not known. Whether such a number exists is also not known. -/
@[category research open, AMS 11]
theorem taxicab_for_5_2_2 : answer(sorry) ↔ ∃ x : ℕ, IsTaxicabFor 5 2 2 x := by
  sorry

/-- Taxicab number for $k=5$ and $m=2$ is not-known for any $n ≥ 2$. Whether such a number exists is also not known. -/
@[category research open, AMS 11]
theorem taxicab_for_5_2_n : answer(sorry) ↔ ∃ n : ℕ, n ≥ 2 ∧ (∃ x : ℕ, IsTaxicabFor 5 2 n x) := by
  sorry

end Taxicab
