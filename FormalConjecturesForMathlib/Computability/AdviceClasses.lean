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

public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Complexity classes with polynomial advice

Advice may be arbitrary and uncomputable, but depends only on input length.
The underlying language belongs to the original class and receives an explicitly
encoded pair. The length bound is one fixed polynomial for all lengths.

Reference: Dell–van Melkebeek, *Satisfiability Allows No Nontrivial Sparsification
unless the Polynomial-Time Hierarchy Collapses* (JACM 2014), §2, p.23:8:
https://pages.cs.wisc.edu/~dieter/Papers/sparsification-jacm.pdf.
-/

@[expose] public section

namespace ComplexityTheory

/-- A polynomial bound on a possibly uncomputable advice sequence. -/
def PolynomialAdvice (a : ℕ → List Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (a n).length ≤ p.eval n

/-- Feed the input and its length-dependent advice to a language. -/
def withAdvice (A : DecisionProblem) (a : ℕ → List Bool) : DecisionProblem :=
  fun x => A (BitstringEncoding.bitEncode (x, a x.length))

/-- Apply the standard polynomial-advice operator to a language class. -/
def WithPolyAdvice (C : ComplexityClass) : ComplexityClass :=
  {L | ∃ (A : DecisionProblem) (a : ℕ → List Bool),
    A ∈ C ∧ PolynomialAdvice a ∧ L = withAdvice A a}

/-- Nondeterministic polynomial time with polynomial-length advice. -/
def NPpoly : ComplexityClass := WithPolyAdvice NP

theorem withAdvice_mem {C : ComplexityClass} {A : DecisionProblem}
    {a : ℕ → List Bool} (hA : A ∈ C) (ha : PolynomialAdvice a) :
    withAdvice A a ∈ WithPolyAdvice C :=
  ⟨A, a, hA, ha, rfl⟩

theorem WithPolyAdvice.mono {C D : ComplexityClass} (h : C ⊆ D) :
    WithPolyAdvice C ⊆ WithPolyAdvice D := by
  rintro L ⟨A, a, hA, ha, hL⟩
  exact ⟨A, a, h hA, ha, hL⟩

/-- Complementing a language commutes with supplying a fixed advice sequence. -/
@[simp]
theorem withAdvice_compl (A : DecisionProblem) (a : ℕ → List Bool) :
    withAdvice Aᶜ a = (withAdvice A a)ᶜ := rfl

/-- A single arbitrary bit per input length is polynomial advice. -/
theorem polynomialAdvice_singleton (b : ℕ → Bool) :
    PolynomialAdvice (fun n => [b n]) := by
  refine ⟨Polynomial.C 1, ?_⟩
  intro n
  simp

/-- Constant advice is permitted, including the empty advice string. -/
theorem polynomialAdvice_const (w : List Bool) :
    PolynomialAdvice (fun _ => w) := by
  refine ⟨Polynomial.C w.length, ?_⟩
  intro n
  simp

/-- Advice cannot distinguish two inputs of equal length. -/
theorem advice_eq_of_length_eq (a : ℕ → List Bool) {x y : List Bool}
    (h : x.length = y.length) : a x.length = a y.length :=
  congrArg a h

end ComplexityTheory
