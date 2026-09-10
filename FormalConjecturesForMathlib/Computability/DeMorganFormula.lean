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

public import FormalConjecturesForMathlib.Computability.BooleanTruthTable

/-!
# De Morgan formulas and disjunctive normal form

De Morgan formulas have binary AND/OR nodes and constant or signed-variable leaves.
Size counts nonconstant leaves, as in Ilango, *The Minimum Formula Size Problem
is (ETH) Hard*, §2: https://rahulilango.com/papers/MFSP-hard.pdf.

DNF size counts terms, not literals, as in Allender–Hellerstein–McCabe–Pitassi–Saks,
*Minimizing DNF Formulas and AC⁰ Circuits Given a Truth Table*, §2:
https://cs.rutgers.edu/~allender/papers/mindnf.pdf.
-/

@[expose] public section

namespace DeMorganFormula

/-- A variable with its required truth value: true is positive, false is negated. -/
abbrev Literal (σ : Type*) := σ × Bool

namespace Literal

/-- Evaluate a signed variable. -/
def eval {σ : Type*} (v : σ → Bool) (l : Literal σ) : Bool := v l.1 == l.2

end Literal

/-- Tree formulas: sharing a subexpression duplicates its leaves. -/
inductive Formula (σ : Type*)
  | const (b : Bool)
  | literal (l : Literal σ)
  | and (a b : Formula σ)
  | or (a b : Formula σ)

namespace Formula

/-- The number of variable occurrences. Constants have size zero. -/
def size {σ : Type*} : Formula σ → ℕ
  | const _ => 0
  | literal _ => 1
  | and a b | or a b => a.size + b.size

/-- Ordinary Boolean semantics. -/
def eval {σ : Type*} (v : σ → Bool) : Formula σ → Bool
  | const b => b
  | literal l => l.eval v
  | and a b => a.eval v && b.eval v
  | or a b => a.eval v || b.eval v

/-- Negation can be pushed to leaves without changing size. -/
def neg {σ : Type*} : Formula σ → Formula σ
  | const b => const (!b)
  | literal (i, b) => literal (i, !b)
  | and a b => or a.neg b.neg
  | or a b => and a.neg b.neg

@[simp]
theorem size_neg {σ : Type*} (f : Formula σ) : f.neg.size = f.size := by
  induction f with
  | const b => rfl
  | literal l => cases l; rfl
  | and a b ha hb => simp [neg, size, ha, hb]
  | or a b ha hb => simp [neg, size, ha, hb]

@[simp]
theorem eval_neg {σ : Type*} (v : σ → Bool) (f : Formula σ) :
    f.neg.eval v = !(f.eval v) := by
  induction f with
  | const b => rfl
  | literal l =>
    rcases l with ⟨i, b⟩
    simp only [neg, eval, Literal.eval]
    cases b <;> cases v i <;> rfl
  | and a b ha hb => simp [neg, eval, ha, hb]
  | or a b ha hb => simp [neg, eval, ha, hb]

/-- A zero-size formula cannot depend on its assignment, despite arbitrarily many constants. -/
theorem eval_eq_of_size_zero {σ : Type*} (f : Formula σ) (h : f.size = 0)
    (v w : σ → Bool) : f.eval v = f.eval w := by
  induction f with
  | const b => rfl
  | literal l => simp [size] at h
  | and a b ha hb =>
    obtain ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp h
    simp only [eval, ha ha0, hb hb0]
  | or a b ha hb =>
    obtain ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp h
    simp only [eval, ha ha0, hb hb0]

end Formula

/-- DNF terms may repeat literals; a contradictory term evaluates to false. -/
abbrev DNF (σ : Type*) := List (List (Literal σ))

namespace DNF

/-- An empty conjunction is true; an empty disjunction is false. -/
def eval {σ : Type*} (v : σ → Bool) (d : DNF σ) : Bool :=
  d.any fun term => term.all (Literal.eval v)

/-- Min-DNF counts the number of terms, not the total number of literals. -/
def size {σ : Type*} (d : DNF σ) : ℕ := d.length

/-- Translate a conjunction into a De Morgan formula. -/
def termFormula {σ : Type*} : List (Literal σ) → Formula σ
  | [] => .const true
  | l :: ls => .and (.literal l) (termFormula ls)

/-- Translate a DNF into a De Morgan formula. -/
def toFormula {σ : Type*} : DNF σ → Formula σ
  | [] => .const false
  | term :: rest => .or (termFormula term) (toFormula rest)

@[simp]
theorem eval_termFormula {σ : Type*} (v : σ → Bool) (term : List (Literal σ)) :
    (termFormula term).eval v = term.all (Literal.eval v) := by
  induction term with
  | nil => rfl
  | cons l ls ih => simp [termFormula, Formula.eval, ih]

@[simp]
theorem eval_toFormula {σ : Type*} (v : σ → Bool) (d : DNF σ) :
    d.toFormula.eval v = d.eval v := by
  induction d with
  | nil => rfl
  | cons term rest ih => simp [toFormula, Formula.eval, ih, eval]

@[simp]
theorem size_termFormula {σ : Type*} (term : List (Literal σ)) :
    (termFormula term).size = term.length := by
  induction term with
  | nil => rfl
  | cons l ls ih => simp [termFormula, Formula.size, ih, Nat.add_comm]

end DNF

end DeMorganFormula
