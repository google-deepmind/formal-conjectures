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

public import FormalConjecturesTest.ForMathlib.SetTheory.Axioms

/-! This file introduces a notiion of some implication being independent of ZFC, but consistent.

-/

@[expose] public section

universe u

/--
A small set of axioms that are independent of ZFC (and Lean's slightly stronger type theory).
This list is should be treated carefully, as any misformalisatio breaks the independet
predicate defined in this file.
Some of them are redundant, but worth including for clarity.

Any change/expansion to it needs to come with a discussion and in particular a reason for
expanding it.

For a justification that this list makes sense, see i.e.

https://math.stackexchange.com/questions/3764313/why-is-ma-not-provable-from-zfc and
https://en.wikipedia.org/wiki/Continuum_hypothesis
-/
def IndependenceSet : Set Prop :=
  {ContinuumHypothesis, NotContinuumHypothesis,
    GeneralizedContinuumHypothesis.{u}, ¬ GeneralizedContinuumHypothesis.{u}, MartinsAxiom,
      ¬ MartinsAxiom, MartinsAxiom ∧ ¬ ContinuumHypothesis}

/-- (Distinct) Members of `IndependenceSet` `(A, B)` satisfying `A → B` (mathematically). -/
def IndependencePairs : Set (Prop × Prop) :=
  { (GeneralizedContinuumHypothesis.{u}, ContinuumHypothesis),
    (GeneralizedContinuumHypothesis.{u}, MartinsAxiom),
    (ContinuumHypothesis, MartinsAxiom),
    (NotContinuumHypothesis, ¬ GeneralizedContinuumHypothesis.{u}),
    (¬ MartinsAxiom, NotContinuumHypothesis),
    (¬ MartinsAxiom, ¬ GeneralizedContinuumHypothesis.{u}),
    (MartinsAxiom ∧ ¬ ContinuumHypothesis, MartinsAxiom),
    (MartinsAxiom ∧ ¬ ContinuumHypothesis, NotContinuumHypothesis),
    (MartinsAxiom ∧ ¬ ContinuumHypothesis, ¬ GeneralizedContinuumHypothesis.{u}) }

/- TODO: prove this (bottleneck is Martin's axiom)
theorem independencePairs_implies {P : Prop × Prop} (hP : P ∈ IndependencePairs) :
    P.1 → P.2 := by sorry
-/

/-- `P` is independent of ZFC and Lean's type theory.
Note: More precisely, the implication can be proved under some set theory axiom known to be
independent and so does its negation.

A proper, exhaustive and `Prop`-valued notion of independence is likely
not possible to define in Lean.

Note we also require a universe parameter (i.e. "independent in universe `v`"),
since GCH might hold in some universes, but not in others. -/
def Independent.{v} (P : Prop) : Prop :=
  (∃ A ∈ IndependenceSet.{v}, A ↔ P) ∨
  (∃ Q ∈ IndependencePairs.{v}, Q.1 → P ∧ P → Q.2)

theorem independent_of_mem_independenceSet {P : Prop} (hP : P ∈ IndependenceSet.{u}) :
    Independent.{u} P := by
  unfold Independent
  left
  exact ⟨P, by simpa⟩

theorem ContinuumHypothesis.independent : Independent.{u} ContinuumHypothesis := by
  apply independent_of_mem_independenceSet
  simp [IndependenceSet]

theorem NotContinuumHypothesis.independent : Independent.{u} NotContinuumHypothesis := by
  apply independent_of_mem_independenceSet
  simp [IndependenceSet]

/- Note the following is *not* true (i.e. `P = CH`):

theorem not_independent_of_true {P : Prop} (h : P) : ¬ Independent.{u} P := by
  sorry

However for every `Q : Prop` that we can actually unconditionally
prove under the standard axioms in Lean (or be able to prove its negation)
(think `True`, `2 = 0`, Fermat's last Theorem, ...),
`Independent Q` will not be provable.

Similarly, for any `Q : Prop`, `¬ Independent Q` will likely never be unconditionally be provable.

-/
