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

public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Straight-line programs

A straight-line program over a commutative ring `R` computes a sequence of values. Each step is
a constant, an input, or the sum, difference or product of two earlier values. The cost of a
program is its number of additions, subtractions and multiplications. Constants and inputs are
free.

This is the division-free arithmetic circuit model of [BCS97, Section 4.1], with unit cost for
each arithmetic operation. A `Matrix.MulCircuit` is a straight-line program that multiplies two
matrices.

*References:*
* [BCS97] P. Bürgisser, M. Clausen and M. A. Shokrollahi,
  [*Algebraic Complexity Theory*](https://doi.org/10.1007/978-3-662-03338-8),
  Grundlehren der mathematischen Wissenschaften 315, Springer, 1997.
-/

namespace StraightLineProgram

/-- One step of a straight-line program over `R`. It reads inputs indexed by `ι` and earlier
values indexed by `σ`. -/
inductive Gate (R ι σ : Type*) where
  | const : R → Gate R ι σ
  | input : ι → Gate R ι σ
  | add : σ → σ → Gate R ι σ
  | sub : σ → σ → Gate R ι σ
  | mul : σ → σ → Gate R ι σ

namespace Gate

variable {R ι σ : Type*}

/-- The value of a gate, given the inputs `x` and the earlier values `v`. -/
def eval [CommRing R] (x : ι → R) (v : σ → R) : Gate R ι σ → R
  | const c => c
  | input i => x i
  | add i j => v i + v j
  | sub i j => v i - v j
  | mul i j => v i * v j

/-- Constants and inputs cost `0`. Each arithmetic operation costs `1`. -/
def cost : Gate R ι σ → ℕ
  | const _ => 0
  | input _ => 0
  | add _ _ => 1
  | sub _ _ => 1
  | mul _ _ => 1

end Gate

end StraightLineProgram

/-- A straight-line program over `R` with inputs indexed by `ι` and `r` steps. Step `k` can read
the values of steps `0, …, k - 1`. -/
inductive StraightLineProgram (R ι : Type*) : ℕ → Type _ where
  | nil : StraightLineProgram R ι 0
  | snoc {r : ℕ} : StraightLineProgram R ι r → StraightLineProgram.Gate R ι (Fin r) →
      StraightLineProgram R ι (r + 1)

namespace StraightLineProgram

variable {R ι : Type*}

/-- The values of all steps of a program on the inputs `x`. -/
def eval [CommRing R] (x : ι → R) : {r : ℕ} → StraightLineProgram R ι r → Fin r → R
  | _, nil => Fin.elim0
  | _, snoc p g => Fin.snoc (p.eval x) (g.eval x (p.eval x))

/-- The number of arithmetic operations in a program. -/
def cost : {r : ℕ} → StraightLineProgram R ι r → ℕ
  | _, nil => 0
  | _, snoc p g => p.cost + g.cost

@[simp]
theorem eval_snoc_last [CommRing R] (x : ι → R) {r : ℕ} (p : StraightLineProgram R ι r)
    (g : Gate R ι (Fin r)) : (p.snoc g).eval x (Fin.last r) = g.eval x (p.eval x) := by
  simp [eval]

@[simp]
theorem eval_snoc_castSucc [CommRing R] (x : ι → R) {r : ℕ} (p : StraightLineProgram R ι r)
    (g : Gate R ι (Fin r)) (i : Fin r) : (p.snoc g).eval x i.castSucc = p.eval x i := by
  simp [eval]

@[simp]
theorem cost_nil : (nil : StraightLineProgram R ι 0).cost = 0 := rfl

@[simp]
theorem cost_snoc {r : ℕ} (p : StraightLineProgram R ι r) (g : Gate R ι (Fin r)) :
    (p.snoc g).cost = p.cost + g.cost := rfl

end StraightLineProgram

namespace Matrix

/-- A straight-line program that reads the entries of an `m × n` matrix and an `n × p` matrix.
The entry `(i, k)` of the result is the value of step `output i k`. -/
structure MulCircuit (R m n p : Type*) where
  /-- The number of steps. -/
  steps : ℕ
  /-- The program. Its inputs are the entries of the two matrices. -/
  program : StraightLineProgram R ((m × n) ⊕ (n × p)) steps
  /-- The step that holds each entry of the result. -/
  output : m → p → Fin steps

namespace MulCircuit

variable {R m n p : Type*}

/-- The matrix that a circuit computes from the matrices `A` and `B`. -/
def eval [CommRing R] (C : MulCircuit R m n p) (A : Matrix m n R) (B : Matrix n p R) :
    Matrix m p R :=
  of fun i k ↦ C.program.eval (Sum.elim (Function.uncurry A) (Function.uncurry B)) (C.output i k)

/-- A circuit is correct if it computes `A * B` for all matrices `A` and `B`. -/
def Correct [CommRing R] [Fintype n] (C : MulCircuit R m n p) : Prop :=
  ∀ A B, C.eval A B = A * B

/-- The number of arithmetic operations in a circuit. -/
def cost (C : MulCircuit R m n p) : ℕ :=
  C.program.cost

end MulCircuit

end Matrix
