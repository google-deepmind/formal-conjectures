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
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Finite division-free arithmetic circuits

A program lists gates in topological order. Binary operations refer to previously
computed gates by zero-based absolute indices; fan-out and repeated use are unrestricted.
The last gate is the output. Empty programs and any invalid reference return `none`.
Evaluation is exact, with no bound on the degree or on intermediate integer bit lengths.

The polynomial semantics uses actual commutative multivariate polynomials. Evaluation
commutes with ring homomorphisms, so it agrees with the executable ring interpreter.
No polynomial-time claim is made about this reference interpreter.

References: Allender et al., *On the Complexity of Numerical Analysis*, §2,
https://people.cs.rutgers.edu/~allender/papers/slp.pdf;
Shpilka–Yehudayoff, *Arithmetic circuits: A survey of recent results and open questions*,
Definition 1.1, https://www.cs.tau.ac.il/~shpilka/publications/SY10.pdf.
-/

@[expose] public section

namespace ArithmeticCircuit

/-- A gate of a division-free arithmetic circuit with binary operations. -/
inductive Gate (σ R : Type)
  | input : σ → Gate σ R
  | constant : R → Gate σ R
  | add : ℕ → ℕ → Gate σ R
  | sub : ℕ → ℕ → Gate σ R
  | mul : ℕ → ℕ → Gate σ R
  deriving DecidableEq

/-- Topologically ordered gates, with the final gate as output. -/
abbrev Program (σ R : Type) := List (Gate σ R)

variable {σ R A B : Type}

namespace Gate

/-- A tagged, finite payload. Indices and integer constants use binary encodings. -/
def code : Gate σ R → ℕ × List σ × List R × List ℕ
  | .input i => (0, [i], [], [])
  | .constant r => (1, [], [r], [])
  | .add i j => (2, [], [], [i, j])
  | .sub i j => (3, [], [], [i, j])
  | .mul i j => (4, [], [], [i, j])

/-- Reject unknown opcodes and payloads of the wrong shape. -/
def decode : ℕ × List σ × List R × List ℕ → Option (Gate σ R)
  | (0, [i], [], []) => some (.input i)
  | (1, [], [r], []) => some (.constant r)
  | (2, [], [], [i, j]) => some (.add i j)
  | (3, [], [], [i, j]) => some (.sub i j)
  | (4, [], [], [i, j]) => some (.mul i j)
  | _ => none

@[simp]
theorem decode_code (g : Gate σ R) : decode g.code = some g := by
  cases g <;> rfl

instance [BitstringEncoding σ] [BitstringEncoding R] : BitstringEncoding (Gate σ R) :=
  BitstringEncoding.ofLeftInverse code decode decode_code

/-- Evaluate one gate using the preceding register values. -/
def eval [Ring A] (v : σ → A) (k : R → A) (registers : List A) :
    Gate σ R → Option A
  | .input i => some (v i)
  | .constant r => some (k r)
  | .add i j => do return (← registers[i]?) + (← registers[j]?)
  | .sub i j => do return (← registers[i]?) - (← registers[j]?)
  | .mul i j => do return (← registers[i]?) * (← registers[j]?)

theorem eval_map [Ring A] [Ring B] (φ : A →+* B) (v : σ → A) (k : R → A)
    (registers : List A) (g : Gate σ R) :
    g.eval (φ ∘ v) (φ ∘ k) (registers.map φ) = (g.eval v k registers).map φ := by
  cases g <;> simp [eval, Option.map_bind, Option.bind_map]

end Gate

/-- Execute the remaining gates, retaining all prior values for shared references. -/
def evalFrom [Ring A] (v : σ → A) (k : R → A) :
    Program σ R → List A → Option (List A)
  | [], registers => some registers
  | g :: rest, registers => do
    let a ← g.eval v k registers
    evalFrom v k rest (registers ++ [a])

/-- Exact execution; malformed or empty circuits have no output. -/
def run [Ring A] (c : Program σ R) (v : σ → A) (k : R → A) : Option A :=
  (evalFrom v k c []).bind List.getLast?

theorem evalFrom_map [Ring A] [Ring B] (φ : A →+* B) (v : σ → A) (k : R → A)
    (c : Program σ R) (registers : List A) :
    evalFrom (φ ∘ v) (φ ∘ k) c (registers.map φ) =
      (evalFrom v k c registers).map (List.map φ) := by
  induction c generalizing registers with
  | nil => rfl
  | cons g rest ih =>
    simp only [evalFrom, Gate.eval_map]
    cases h : g.eval v k registers with
    | none => simp
    | some a => simpa [h] using ih (registers ++ [a])

theorem run_map [Ring A] [Ring B] (φ : A →+* B) (v : σ → A) (k : R → A)
    (c : Program σ R) :
    run c (φ ∘ v) (φ ∘ k) = (run c v k).map φ := by
  have h := evalFrom_map φ v k c []
  simp only [List.map_nil] at h
  simp [run, h, Option.bind_map, Option.map_bind]

/-- The polynomial computed by a circuit, not its values on a finite sample. -/
noncomputable def polynomial [CommRing R] (c : Program σ R) :
    Option (MvPolynomial σ R) :=
  run c MvPolynomial.X MvPolynomial.C

/-- Polynomial denotation agrees with exact evaluation on every assignment. -/
theorem eval_polynomial [CommRing R] (c : Program σ R) (v : σ → R) :
    (polynomial c).map (MvPolynomial.eval v) = run c v id := by
  rw [polynomial, ← run_map]
  congr 1
  · funext i
    exact MvPolynomial.eval_X i
  · funext r
    exact MvPolynomial.eval_C r

/-- Over an infinite integral domain, identity means zero on every assignment.
The equivalence also rules out malformed and empty circuits. -/
theorem polynomial_eq_zero_iff [CommRing R] [IsDomain R] [Infinite R]
    (c : Program σ R) :
    polynomial c = some 0 ↔ ∀ v : σ → R, run c v id = some 0 := by
  constructor
  · intro h v
    rw [← eval_polynomial, h]
    simp
  · intro h
    cases hp : polynomial c with
    | none =>
      have hv := h (fun _ => 0)
      rw [← eval_polynomial, hp] at hv
      contradiction
    | some p =>
      have hz : p = 0 := MvPolynomial.funext fun v => by
        have hv := h v
        rw [← eval_polynomial, hp] at hv
        simpa using hv
      simp [hz]

end ArithmeticCircuit
