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

public import FormalConjecturesForMathlib.Computability.BooleanCircuit
public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Nonuniform polynomial-size Boolean circuits

Circuit families have one circuit for each input length, with no computability
requirement on that choice. The bound is fixed before quantifying over lengths.

We use De Morgan DAGs, counting AND/OR gates with free NOT gates and hardwired
Boolean constants. These basis and size conventions preserve polynomial-size
computability. Constants also let circuits act on the unique zero-bit input.

References: Williams, *Algorithms for Circuits and Circuits for Algorithms*
(2014), §II and Definitions 3.1–3.2:
https://people.csail.mit.edu/rrw/ccc14-survey.pdf.
-/

@[expose] public section

namespace ComplexityTheory

/-- An n-input circuit with hardwired false/true references. -/
abbrev BooleanFamilyCircuit (n : ℕ) := BooleanCircuit.Circuit (Bool ⊕ Fin n)

namespace BooleanFamilyCircuit

/-- Hardwired inputs evaluate to themselves; variable inputs read the assignment. -/
def eval {n : ℕ} (c : BooleanFamilyCircuit n) (v : Fin n → Bool) : Bool :=
  BooleanCircuit.Circuit.eval c (Sum.elim id v)

/-- A constant circuit, also available at arity zero. -/
def const (n : ℕ) (b : Bool) : BooleanFamilyCircuit n :=
  .output (.inl (.inl b))

@[simp]
theorem eval_const (n : ℕ) (b : Bool) (v : Fin n → Bool) :
    (const n b).eval v = b := rfl

@[simp]
theorem size_const (n : ℕ) (b : Bool) : (const n b).size = 0 := rfl

@[simp]
theorem eval_neg {n : ℕ} (c : BooleanFamilyCircuit n) (v : Fin n → Bool) :
    eval c.neg v = !(c.eval v) :=
  BooleanCircuit.Program.eval_neg _ _ _

end BooleanFamilyCircuit

/-- One bounded circuit for every length, correct on every assignment of that length. -/
def HasCircuitSize (L : DecisionProblem) (s : ℕ → ℕ) : Prop :=
  ∀ n, ∃ c : BooleanFamilyCircuit n, c.size ≤ s n ∧
    ∀ v : Fin n → Bool, c.eval v = L (List.ofFn v)

/-- Languages computed by nonuniform circuit families of polynomial size. -/
def Ppoly : Set DecisionProblem :=
  {L | ∃ k : ℕ, 1 ≤ k ∧ HasCircuitSize L (fun n => n ^ k + k)}

theorem HasCircuitSize.mono {L : DecisionProblem} {s t : ℕ → ℕ}
    (h : HasCircuitSize L s) (hst : ∀ n, s n ≤ t n) : HasCircuitSize L t := by
  intro n
  obtain ⟨c, hc, hL⟩ := h n
  exact ⟨c, hc.trans (hst n), hL⟩

theorem HasCircuitSize.compl {L : DecisionProblem} {s : ℕ → ℕ}
    (h : HasCircuitSize L s) : HasCircuitSize Lᶜ s := by
  intro n
  obtain ⟨c, hc, hL⟩ := h n
  refine ⟨c.neg, by simpa using hc, ?_⟩
  intro v
  change BooleanFamilyCircuit.eval c.neg v = !(L (List.ofFn v))
  rw [BooleanFamilyCircuit.eval_neg, hL]

@[simp]
theorem hasCircuitSize_compl {L : DecisionProblem} {s : ℕ → ℕ} :
    HasCircuitSize Lᶜ s ↔ HasCircuitSize L s := by
  constructor
  · intro h
    simpa using h.compl
  · exact HasCircuitSize.compl

@[simp]
theorem mem_Ppoly_compl (L : DecisionProblem) : Lᶜ ∈ Ppoly ↔ L ∈ Ppoly := by
  simp only [Ppoly, Set.mem_ofPred_eq, hasCircuitSize_compl]

/-- Even an arbitrary, uncomputable dependence on length has zero-size circuits. -/
theorem hasCircuitSize_length (b : ℕ → Bool) :
    HasCircuitSize (fun x => b x.length) (fun _ => 0) := by
  intro n
  refine ⟨BooleanFamilyCircuit.const n (b n), Nat.le_refl _, ?_⟩
  intro v
  simp

theorem length_mem_Ppoly (b : ℕ → Bool) :
    (fun x => b x.length) ∈ Ppoly :=
  ⟨1, Nat.le_refl _, (hasCircuitSize_length b).mono (fun _ => Nat.zero_le _)⟩

/-- Every proposed circuit family must also compute the empty input correctly. -/
theorem HasCircuitSize.empty {L : DecisionProblem} {s : ℕ → ℕ}
    (h : HasCircuitSize L s) :
    ∃ c : BooleanFamilyCircuit 0, c.size ≤ s 0 ∧ c.eval Fin.elim0 = L [] := by
  obtain ⟨c, hc, hL⟩ := h 0
  exact ⟨c, hc, by simpa using hL Fin.elim0⟩

end ComplexityTheory
