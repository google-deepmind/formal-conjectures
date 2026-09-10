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

public import FormalConjecturesForMathlib.Computability.PropositionalSyntax

/-!
# A concrete Frege calculus

The six axiom schemes and modus ponens are exactly the negation/implication
example in Cook–Reckhow, *The Relative Efficiency of Propositional Proof Systems*
(1979), §2, pp.39–40: https://www.karlin.mff.cuni.cz/~krajicek/cr79.pdf.

Each axiom recognizer checks the syntax of one scheme, including equality of
repeated metavariables. Modus ponens uses only previously checked formulas.
No semantic tautology test is an inference rule.
-/

@[expose] public section

namespace PropositionalProof.Frege

open Formula

def axiom1 : Formula → Bool
  | .imp a (.imp _ a') => a == a'
  | _ => false

def axiom2 : Formula → Bool
  | .imp (.imp c (.imp b a)) (.imp (.imp c' b') (.imp c'' a')) =>
    c == c' && c == c'' && b == b' && a == a'
  | _ => false

def axiom3 : Formula → Bool
  | .imp (.imp d (.imp b a)) (.imp b' (.imp d' a')) =>
    d == d' && b == b' && a == a'
  | _ => false

def axiom4 : Formula → Bool
  | .imp (.imp b a) (.imp (.neg a') (.neg b')) => a == a' && b == b'
  | _ => false

def axiom5 : Formula → Bool
  | .imp (.neg (.neg a)) a' => a == a'
  | _ => false

def axiom6 : Formula → Bool
  | .imp a (.neg (.neg a')) => a == a'
  | _ => false

/-- All six tests are independent; overlapping syntactic patterns are allowed. -/
def isAxiom (p : Formula) : Bool :=
  axiom1 p || axiom2 p || axiom3 p || axiom4 p || axiom5 p || axiom6 p

theorem axiom1_sound {p : Formula} (h : axiom1 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom1 at h
  split at h
  next a b a' =>
    have he : a = a' := by simpa using h
    subst a'
    cases ha : a.eval v <;> cases hb : b.eval v <;> simp [eval, ha, hb]
  next => simp at h

theorem axiom2_sound {p : Formula} (h : axiom2 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom2 at h
  split at h
  next c b a c' b' c'' a' =>
    have he : c = c' ∧ c = c'' ∧ b = b' ∧ a = a' := by simpa [and_assoc] using h
    rcases he with ⟨rfl, rfl, rfl, rfl⟩
    cases ha : a.eval v <;> cases hb : b.eval v <;> cases hc : c.eval v <;>
      simp [eval, ha, hb, hc]
  next => simp at h

theorem axiom3_sound {p : Formula} (h : axiom3 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom3 at h
  split at h
  next d b a b' d' a' =>
    have he : d = d' ∧ b = b' ∧ a = a' := by simpa [and_assoc] using h
    rcases he with ⟨rfl, rfl, rfl⟩
    cases ha : a.eval v <;> cases hb : b.eval v <;> cases hd : d.eval v <;>
      simp [eval, ha, hb, hd]
  next => simp at h

theorem axiom4_sound {p : Formula} (h : axiom4 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom4 at h
  split at h
  next b a a' b' =>
    have he : a = a' ∧ b = b' := by simpa using h
    rcases he with ⟨rfl, rfl⟩
    cases ha : a.eval v <;> cases hb : b.eval v <;> simp [eval, ha, hb]
  next => simp at h

theorem axiom5_sound {p : Formula} (h : axiom5 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom5 at h
  split at h
  next a a' =>
    have he : a = a' := by simpa using h
    subst a'
    cases ha : a.eval v <;> simp [eval, ha]
  next => simp at h

theorem axiom6_sound {p : Formula} (h : axiom6 p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  unfold axiom6 at h
  split at h
  next a a' =>
    have he : a = a' := by simpa using h
    subst a'
    cases ha : a.eval v <;> simp [eval, ha]
  next => simp at h

theorem isAxiom_sound {p : Formula} (h : isAxiom p = true) (v : ℕ → Bool) :
    p.eval v = true := by
  simp only [isAxiom, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact axiom1_sound h v
  · exact axiom2_sound h v
  · exact axiom3_sound h v
  · exact axiom4_sound h v
  · exact axiom5_sound h v
  · exact axiom6_sound h v

/-- Both the implication and its antecedent must occur in the earlier context. -/
def modusPonens (earlier : List Formula) (p : Formula) : Bool :=
  earlier.any fun q => match q with
    | .imp a b => b == p && earlier.contains a
    | _ => false

theorem modusPonens_sound {earlier : List Formula} {p : Formula}
    (h : modusPonens earlier p = true) (v : ℕ → Bool)
    (hv : ∀ q ∈ earlier, q.eval v = true) : p.eval v = true := by
  obtain ⟨q, hq, hr⟩ := List.any_eq_true.mp h
  cases q with
  | var n => simp at hr
  | neg q => simp at hr
  | imp a b =>
    have he : b = p ∧ a ∈ earlier := by simpa using hr
    rcases he with ⟨rfl, ha⟩
    have hi := hv (.imp a b) hq
    simpa [eval, hv a ha] using hi

def step (earlier : List Formula) (p : Formula) : Bool :=
  isAxiom p || modusPonens earlier p

theorem step_sound {earlier : List Formula} {p : Formula}
    (h : step earlier p = true) (v : ℕ → Bool)
    (hv : ∀ q ∈ earlier, q.eval v = true) : p.eval v = true := by
  have hr : isAxiom p = true ∨ modusPonens earlier p = true := by simpa [step] using h
  rcases hr with h | h
  · exact isAxiom_sound h v
  · exact modusPonens_sound h v hv

end PropositionalProof.Frege
