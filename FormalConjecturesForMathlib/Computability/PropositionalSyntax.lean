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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Function.Basic

/-!
# Propositional syntax for proof complexity

Formulas use the complete basis of negation and implication, with binary natural
number variable names. Syntax is a tree, not a circuit; repeated subformulas are
stored repeatedly. Prefix tokens are encoded as a flat list, avoiding a recursive
framing overhead exponential in formula depth.

Reference: Cook–Reckhow, *The Relative Efficiency of Propositional Proof Systems*
(1979), §1–2: https://www.karlin.mff.cuni.cz/~krajicek/cr79.pdf.
This module supplies syntax, truth semantics, substitution and a reversible
encoding. It does not assert a polynomial-time parser or a machine simulation.
-/

@[expose] public section

namespace PropositionalProof

inductive Formula
  | var : ℕ → Formula
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq

namespace Formula

def eval (a : ℕ → Bool) : Formula → Bool
  | .var v => a v
  | .neg p => !(eval a p)
  | .imp p q => !(eval a p) || eval a q

def support : Formula → Finset ℕ
  | .var v => {v}
  | .neg p => support p
  | .imp p q => support p ∪ support q

theorem eval_congr {a b : ℕ → Bool} (p : Formula)
    (h : ∀ v ∈ p.support, a v = b v) : p.eval a = p.eval b := by
  induction p with
  | var v => exact h v (by simp [support])
  | neg p ih => simp only [eval, ih h]
  | imp p q ihp ihq =>
    have hp : ∀ v ∈ p.support, a v = b v := fun v hv => h v (by simp [support, hv])
    have hq : ∀ v ∈ q.support, a v = b v := fun v hv => h v (by simp [support, hv])
    simp only [eval, ihp hp, ihq hq]

theorem eval_update {a : ℕ → Bool} {p : Formula} {v : ℕ} (b : Bool)
    (hv : v ∉ p.support) : p.eval (Function.update a v b) = p.eval a := by
  apply eval_congr
  intro w hw
  have hwv : w ≠ v := by rintro rfl; exact hv hw
  simp [Function.update, hwv]

def subst (σ : ℕ → Formula) : Formula → Formula
  | .var v => σ v
  | .neg p => .neg (subst σ p)
  | .imp p q => .imp (subst σ p) (subst σ q)

theorem eval_subst (a : ℕ → Bool) (σ : ℕ → Formula) (p : Formula) :
    (p.subst σ).eval a = p.eval (fun v => (σ v).eval a) := by
  induction p <;> simp_all [subst, eval]

/-- Conjunction as an abbreviation in the negation/implication basis. -/
def conj (p q : Formula) : Formula := .neg (.imp p (.neg q))

/-- Equivalence used in extension axioms. Both operands are stored twice. -/
def iff (p q : Formula) : Formula := conj (.imp p q) (.imp q p)

@[simp]
theorem eval_conj (a : ℕ → Bool) (p q : Formula) :
    (conj p q).eval a = (p.eval a && q.eval a) := by
  simp [conj, eval]

@[simp]
theorem eval_iff (a : ℕ → Bool) (p q : Formula) :
    (iff p q).eval a = (p.eval a == q.eval a) := by
  cases hp : p.eval a <;> cases hq : q.eval a <;> simp [iff, conj, eval, hp, hq]

/-- Truth under every assignment to the variables that actually occur. -/
def Tautology (p : Formula) : Prop :=
  ∀ chosen ⊆ p.support, p.eval (fun v => decide (v ∈ chosen)) = true

instance (p : Formula) : Decidable p.Tautology := by
  unfold Tautology
  infer_instance

theorem tautology_iff (p : Formula) : p.Tautology ↔ ∀ a : ℕ → Bool, p.eval a = true := by
  constructor
  · intro h a
    let chosen := p.support.filter (fun v => a v = true)
    have hc : chosen ⊆ p.support := Finset.filter_subset _ _
    have he : p.eval (fun v => decide (v ∈ chosen)) = p.eval a := by
      apply eval_congr
      intro v hv
      simp [chosen, hv]
    exact he ▸ h chosen hc
  · intro h chosen _
    exact h _

/-- One token per syntax node; 0 and 1 are reserved for the two connectives. -/
def tokens : Formula → List ℕ
  | .var v => [v + 2]
  | .neg p => 0 :: tokens p
  | .imp p q => 1 :: (tokens p ++ tokens q)

def nodes : Formula → ℕ
  | .var _ => 1
  | .neg p => nodes p + 1
  | .imp p q => nodes p + nodes q + 1

@[simp]
theorem tokens_length (p : Formula) : p.tokens.length = p.nodes := by
  induction p <;> simp_all [tokens, nodes]

/-- Parse one prefix formula. Fuel bounds recursion, not the values of variable names. -/
def parse : ℕ → List ℕ → Option (Formula × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, 0 :: rest => (parse fuel rest).map (fun p => (.neg p.1, p.2))
  | fuel + 1, 1 :: rest =>
    (parse fuel rest).bind fun p =>
      (parse fuel p.2).map (fun q => (.imp p.1 q.1, q.2))
  | _ + 1, (v + 2) :: rest => some (.var v, rest)

theorem parse_tokens (p : Formula) (rest : List ℕ) (fuel : ℕ) (hf : p.nodes ≤ fuel) :
    parse fuel (p.tokens ++ rest) = some (p, rest) := by
  induction p generalizing fuel rest with
  | var v =>
    cases fuel with
    | zero => simp [nodes] at hf
    | succ fuel => rfl
  | neg p ih =>
    cases fuel with
    | zero => simp [nodes] at hf
    | succ fuel =>
      have hp : p.nodes ≤ fuel := by simp only [nodes] at hf; omega
      simpa [tokens, parse] using congrArg (Option.map (fun q => (Formula.neg q.1, q.2)))
        (ih rest fuel hp)
  | imp p q ihp ihq =>
    cases fuel with
    | zero => simp [nodes] at hf
    | succ fuel =>
      have hp : p.nodes ≤ fuel := by simp only [nodes] at hf; omega
      have hq : q.nodes ≤ fuel := by simp only [nodes] at hf; omega
      simp only [tokens, List.cons_append, List.append_assoc, parse,
        ihp (q.tokens ++ rest) fuel hp, Option.bind_some, ihq rest fuel hq, Option.map_some]

/-- Reject truncated trees and trailing tokens. -/
def ofTokens (input : List ℕ) : Option Formula :=
  (parse input.length input).bind (fun p => if p.2 = [] then some p.1 else none)

@[simp]
theorem ofTokens_tokens (p : Formula) : ofTokens p.tokens = some p := by
  have h := parse_tokens p [] p.tokens.length (by simp)
  simp only [List.append_nil] at h
  simp only [ofTokens, h, Option.bind_some, ite_true]

instance : BitstringEncoding Formula :=
  BitstringEncoding.ofLeftInverse tokens ofTokens ofTokens_tokens

/-- Size counts the actual encoded symbols, including binary variable names. -/
def size (p : Formula) : ℕ := (BitstringEncoding.bitEncode p).length

end Formula

end PropositionalProof
