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
module

public import Init

/-!
# Internal set-theoretic models for partition relations

Membership, functions, cardinal comparisons, and colorings are interpreted inside
an arbitrary nonempty membership structure. Separation and replacement use finite
first-order formulas with parameters. Models need not be externally well founded.

*Reference:* [Erdős Problem 474](https://www.erdosproblems.com/474).
-/

@[expose] public section

namespace Erdos474Model

/-- First-order membership formulas with exactly `n` available free variables.
A universal binder adds variable zero and shifts the existing variables. -/
inductive Formula : Nat → Type
  | falsum {n : Nat} : Formula n
  | equal {n : Nat} : Fin n → Fin n → Formula n
  | member {n : Nat} : Fin n → Fin n → Formula n
  | implies {n : Nat} : Formula n → Formula n → Formula n
  | all {n : Nat} : Formula (n + 1) → Formula n

structure Universe where
  Carrier : Type
  membership : Carrier → Carrier → Prop
  inhabited : Nonempty Carrier

namespace Universe
variable (U : Universe)

abbrev Mem := U.membership

/-- Tarski semantics, with a finite tuple of parameters. -/
def Satisfies (U : Universe) : {n : Nat} → Formula n → (Fin n → U.Carrier) → Prop
  | _, .falsum, _ => False
  | _, .equal i j, e => e i = e j
  | _, .member i j, e => U.Mem (e i) (e j)
  | _, .implies p q, e => Satisfies U p e → Satisfies U q e
  | _, .all p, e => ∀ x, Satisfies U p (Fin.cases x e)

variable {U}
def Subset (a b : U.Carrier) : Prop := ∀ x, U.Mem x a → U.Mem x b
def Empty (a : U.Carrier) : Prop := ∀ x, ¬ U.Mem x a
def Pair (a b p : U.Carrier) : Prop := ∀ x, U.Mem x p ↔ x = a ∨ x = b
def Union (a u : U.Carrier) : Prop :=
  ∀ x, U.Mem x u ↔ ∃ y, U.Mem y a ∧ U.Mem x y
def Power (a p : U.Carrier) : Prop := ∀ x, U.Mem x p ↔ Subset x a
def Successor (a s : U.Carrier) : Prop := ∀ x, U.Mem x s ↔ U.Mem x a ∨ x = a
def Inductive (a : U.Carrier) : Prop :=
  (∃ z, Empty z ∧ U.Mem z a) ∧
  ∀ x, U.Mem x a → ∃ s, Successor x s ∧ U.Mem s a
/-- The least inductive set, specified internally. -/
def Omega (w : U.Carrier) : Prop := Inductive w ∧ ∀ a, Inductive a → Subset w a

def OrderedPair (a b p : U.Carrier) : Prop :=
  ∃ s t, Pair a a s ∧ Pair a b t ∧ Pair s t p

def Edge (f x y : U.Carrier) : Prop :=
  ∃ p, OrderedPair x y p ∧ U.Mem p f

/-- A set which is the graph of a total function `a → b`. -/
def Function (f a b : U.Carrier) : Prop :=
  (∀ p, U.Mem p f → ∃ x y, U.Mem x a ∧ U.Mem y b ∧ OrderedPair x y p) ∧
  (∀ x, U.Mem x a → ∃ y, U.Mem y b ∧ Edge f x y) ∧
  (∀ x y z, Edge f x y → Edge f x z → y = z)

def Injection (f a b : U.Carrier) : Prop :=
  Function f a b ∧ ∀ x y z, Edge f x z → Edge f y z → x = y

def Bijection (f a b : U.Carrier) : Prop :=
  Injection f a b ∧ ∀ y, U.Mem y b → ∃ x, U.Mem x a ∧ Edge f x y

def Embeds (a b : U.Carrier) : Prop := ∃ f, Injection f a b

def Transitive (a : U.Carrier) : Prop := ∀ x y, U.Mem x a → U.Mem y x → U.Mem y a

/-- A transitive set internally well ordered by membership. The minimum condition
ranges over internal nonempty subsets, not all external subsets of the carrier. -/
def Ordinal (a : U.Carrier) : Prop :=
  Transitive a ∧
  (∀ x, U.Mem x a → ¬ U.Mem x x) ∧
  (∀ x y z, U.Mem x a → U.Mem y a → U.Mem z a →
    U.Mem x y → U.Mem y z → U.Mem x z) ∧
  (∀ x y, U.Mem x a → U.Mem y a → x = y ∨ U.Mem x y ∨ U.Mem y x) ∧
  ∀ b, Subset b a → (∃ x, U.Mem x b) →
    ∃ x, U.Mem x b ∧ ∀ y, U.Mem y b → ¬ U.Mem y x

/-- The first uncountable initial ordinal, relative to internal omega. -/
def AlephOne (w a : U.Carrier) : Prop :=
  Ordinal a ∧ ¬ Embeds a w ∧ ∀ b, U.Mem b a → Embeds b w

/-- The next initial ordinal, relative to internal aleph one. -/
def AlephTwo (a b : U.Carrier) : Prop :=
  Ordinal b ∧ ¬ Embeds b a ∧ ∀ c, U.Mem c b → Embeds c a

def Three (t : U.Carrier) : Prop :=
  ∃ z o d, Empty z ∧ Successor z o ∧ Successor o d ∧ Successor d t

/-- Domain of ordered distinct pairs. Symmetry below identifies the two orders. -/
def DistinctPairs (r d : U.Carrier) : Prop :=
  ∀ p, U.Mem p d ↔ ∃ x y, U.Mem x r ∧ U.Mem y r ∧ x ≠ y ∧ OrderedPair x y p

def PairColor (c x y i : U.Carrier) : Prop :=
  ∃ p, OrderedPair x y p ∧ Edge c p i

def SymmetricColoring (r t d c : U.Carrier) : Prop :=
  DistinctPairs r d ∧ Function c d t ∧
  ∀ x y i, U.Mem x r → U.Mem y r → x ≠ y →
    (PairColor c x y i ↔ PairColor c y x i)

/-- Every internal uncountable subset realizes all three colors. -/
def AllColorsOnUncountable (w r t c : U.Carrier) : Prop :=
  ∀ a, Subset a r → ¬ Embeds a w →
    ∀ i, U.Mem i t → ∃ x y, U.Mem x a ∧ U.Mem y a ∧ x ≠ y ∧ PairColor c x y i

/-- The positive coloring assertion in this particular model. -/
def ColoringAssertion (w r t : U.Carrier) : Prop :=
  ∃ d c, SymmetricColoring r t d c ∧ AllColorsOnUncountable w r t c

variable (U)

/-- Full ZFC: the two formula schemes are first-order schemes with parameters. -/
structure ZFC : Prop where
  extensionality : ∀ a b : U.Carrier, (∀ x, U.Mem x a ↔ U.Mem x b) → a = b
  empty : ∃ a : U.Carrier, Empty a
  pairing : ∀ a b : U.Carrier, ∃ p, Pair a b p
  union : ∀ a : U.Carrier, ∃ u, Union a u
  power : ∀ a : U.Carrier, ∃ p, Power a p
  infinity : ∃ a : U.Carrier, Inductive a
  foundation : ∀ a : U.Carrier, (∃ x, U.Mem x a) →
    ∃ x, U.Mem x a ∧ ¬ ∃ y, U.Mem y a ∧ U.Mem y x
  separation : ∀ (n : Nat) (p : Formula (n + 1)) (e : Fin n → U.Carrier)
    (a : U.Carrier), ∃ b, ∀ x, U.Mem x b ↔ U.Mem x a ∧ U.Satisfies p (Fin.cases x e)
  replacement : ∀ (n : Nat) (p : Formula (n + 2)) (e : Fin n → U.Carrier)
    (a : U.Carrier),
    (∀ x, U.Mem x a → ∃ y, U.Satisfies p (Fin.cases x (Fin.cases y e)) ∧
      ∀ z, U.Satisfies p (Fin.cases x (Fin.cases z e)) → z = y) →
    ∃ b, ∀ y, U.Mem y b ↔ ∃ x, U.Mem x a ∧ U.Satisfies p (Fin.cases x (Fin.cases y e))
  /-- Choice as a choice function on every internal family of nonempty sets. -/
  choice : ∀ a : U.Carrier, (∀ x, U.Mem x a → ∃ y, U.Mem y x) →
    ∃ u f, Union a u ∧ Function f a u ∧
      ∀ x y, U.Mem x a → Edge f x y → U.Mem y x

/-- The model has continuum aleph two but no coloring with the stated property. -/
def CounterexampleTheory : Prop :=
  ZFC U ∧ ∃ w a₁ a₂ r t : U.Carrier,
    Omega w ∧ AlephOne w a₁ ∧ AlephTwo a₁ a₂ ∧ Power w r ∧ Three t ∧
    (∃ f, Bijection f r a₂) ∧ ¬ ColoringAssertion w r t


/-- Standard positive partition-arrow formulation: every symmetric coloring has
an internally uncountable subset which omits at least one color. -/
def PositiveArrow (w r t : U.Carrier) : Prop :=
  ∀ d c, SymmetricColoring r t d c →
    ∃ a, Subset a r ∧ ¬ Embeds a w ∧
      ∃ i, U.Mem i t ∧ ¬ ∃ x y, U.Mem x a ∧ U.Mem y a ∧ x ≠ y ∧ PairColor c x y i

/-- Duality of the negative coloring and positive partition formulations. -/
theorem positiveArrow_iff_not_coloring (w r t : U.Carrier) :
    U.PositiveArrow w r t ↔ ¬ ColoringAssertion w r t := by
  classical
  simp only [PositiveArrow, ColoringAssertion, AllColorsOnUncountable,
    not_exists, not_and, Classical.not_forall, exists_prop]

/-- The same countermodel theory, expressed with a positive partition arrow. -/
def CounterexampleArrowTheory : Prop :=
  ZFC U ∧ ∃ w a₁ a₂ r t : U.Carrier,
    Omega w ∧ AlephOne w a₁ ∧ AlephTwo a₁ a₂ ∧ Power w r ∧ Three t ∧
    (∃ f, Bijection f r a₂) ∧ U.PositiveArrow w r t

theorem counterexampleTheory_iff_arrow : U.CounterexampleTheory ↔ U.CounterexampleArrowTheory := by
  simp only [CounterexampleTheory, CounterexampleArrowTheory,
    positiveArrow_iff_not_coloring]

end Universe

/-- Full semantic consistency question. This is a proposition, not a theorem. -/
def SemanticConsistencyQuestion : Prop := ∃ U : Universe, U.CounterexampleTheory

/-- Equivalent semantic consistency target in positive-arrow form. -/
def SemanticArrowConsistencyQuestion : Prop := ∃ U : Universe, U.CounterexampleArrowTheory

theorem semanticConsistency_iff_arrow :
    SemanticConsistencyQuestion ↔ SemanticArrowConsistencyQuestion := by
  simp only [SemanticConsistencyQuestion, SemanticArrowConsistencyQuestion,
    Universe.counterexampleTheory_iff_arrow]

end Erdos474Model
