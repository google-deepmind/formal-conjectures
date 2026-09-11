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
public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Cook–Reckhow proof systems and simulations

A proof system is a total polynomial-time map from binary proofs to formulas,
with range exactly the tautologies. Polynomial time uses Mathlib's actual TM2
model through `ComplexityTheory.IsPolyTime`, not an unspecified complexity predicate.

Simulation requires a polynomial bound on translated proof length.
P-simulation additionally requires one deterministic polynomial-time translator.
The translator, coefficient and exponent may depend on the two systems, but
not on the proof being translated.

References: Cook–Reckhow (1979), Definitions 1.3 and 1.5;
Krajíček, *The Cook-Reckhow definition*, Definitions 1.1 and 2.1,
https://arxiv.org/abs/1909.03691.
We fix the negation/implication language, as permitted by the original definition.
-/

@[expose] public section

namespace PropositionalProof

/-- A functional propositional proof system with exact range and an actual polynomial-time
machine. The canonical encoding of binary proof lists has linear framing overhead. -/
structure CookReckhow where
  output : List Bool → Formula
  polytime : ComplexityTheory.IsPolyTime output
  sound : ∀ w, (output w).Tautology
  complete : ∀ p : Formula, p.Tautology → ∃ w, output w = p

namespace CookReckhow

theorem range_iff (f : CookReckhow) (p : Formula) :
    (∃ w, f.output w = p) ↔ p.Tautology := by
  constructor
  · rintro ⟨w, rfl⟩
    exact f.sound w
  · exact f.complete p

/-- A length-bounded translation, with no computability condition. -/
def Simulates (f g : CookReckhow) : Prop :=
  ∃ (h : List Bool → List Bool) (C k : ℕ),
    ∀ w, f.output (h w) = g.output w ∧ (h w).length ≤ C * (w.length + 1) ^ k

/-- One polynomial-time translation, in addition to a polynomial output-size bound. -/
def PSimulates (f g : CookReckhow) : Prop :=
  ∃ (h : List Bool → List Bool), ComplexityTheory.IsPolyTime h ∧
    ∃ C k : ℕ, ∀ w,
      f.output (h w) = g.output w ∧ (h w).length ≤ C * (w.length + 1) ^ k

def Optimal (f : CookReckhow) : Prop := ∀ g : CookReckhow, f.Simulates g

def POptimal (f : CookReckhow) : Prop := ∀ g : CookReckhow, f.PSimulates g

theorem psimulates_implies_simulates {f g : CookReckhow} (h : f.PSimulates g) :
    f.Simulates g := by
  obtain ⟨h, _, C, k, hh⟩ := h
  exact ⟨h, C, k, hh⟩

theorem poptimal_implies_optimal {f : CookReckhow} (h : f.POptimal) : f.Optimal :=
  fun g => psimulates_implies_simulates (h g)

theorem psimulates_self (f : CookReckhow) : f.PSimulates f := by
  refine ⟨id, ComplexityTheory.isPolyTime_id, 1, 1, ?_⟩
  intro w
  simp

theorem simulates_self (f : CookReckhow) : f.Simulates f :=
  psimulates_implies_simulates f.psimulates_self

/-- The nonuniform simulation notion is equivalent to the proof-by-proof size bound.
Classical choice constructs a translator here, but makes no time-complexity claim. -/
theorem simulates_iff (f g : CookReckhow) :
    f.Simulates g ↔ ∃ C k : ℕ, ∀ w : List Bool, ∃ v : List Bool,
      f.output v = g.output w ∧ v.length ≤ C * (w.length + 1) ^ k := by
  constructor
  · rintro ⟨h, C, k, hh⟩
    exact ⟨C, k, fun w => ⟨h w, hh w⟩⟩
  · rintro ⟨C, k, hh⟩
    choose h he using hh
    exact ⟨h, C, k, he⟩

end CookReckhow

end PropositionalProof
