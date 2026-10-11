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

public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Computability.Encoding
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Explicit Boolean families and circuit lower bounds

We use CSLib's circuits over the basis of all sixteen binary Boolean operations.
Each operation costs one gate. Inputs, wires, and designated outputs are free.

`Explicit` requires a single deterministic multitape Turing machine to print the truth table
on unary input in time polynomial in the table length. This is the time scale
$2^{O(n)}$, where $n$ is the number of variables. The definition differs from the
$\mathsf{NP}$ convention for explicitness in Jukna, Section 1.5.1.

*Reference:* Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*,
Springer, 2012, Sections 1.2 and 1.5.1 of
[Chapter 1](https://web.vu.lt/mif/s.jukna/boolean/chapter1.pdf).
-/

@[expose] public section

namespace ComplexityTheory

open Cslib.Circuits Filter

/-- A Boolean function for each input length. -/
abbrev BooleanFamily := (n : ℕ) → (Fin n → Bool) → Bool

/-- The basis $B_2$ of all sixteen binary Boolean operations. -/
abbrev binarySignature : Signature where
  Op := Bool → Bool → Bool
  Arity _ := 2

/-- The usual interpretation of the binary Boolean operations. -/
def binaryInterpretation : Interpretation binarySignature Bool :=
  fun op x => op (x 0) (x 1)

/-- The truth table in lexicographic order, with `false` before `true` and coordinate zero first. -/
def truthTable : {n : ℕ} → ((Fin n → Bool) → Bool) → List Bool
  | 0, f => [f Fin.elim0]
  | _ + 1, f => truthTable (fun x => f (Fin.cons false x)) ++
      truthTable (fun x => f (Fin.cons true x))

@[simp] theorem truthTable_length {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (truthTable f).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [truthTable, ih, pow_succ, Nat.mul_two]

theorem truthTable_injective {n : ℕ} : Function.Injective (@truthTable n) := by
  induction n with
  | zero =>
    intro f g h
    funext x
    have hx : x = Fin.elim0 := funext fun i => i.elim0
    subst x
    simpa [truthTable] using h
  | succ n ih =>
    intro f g h
    obtain ⟨hfalse, htrue⟩ := List.append_inj h (by simp)
    have hfalse := ih hfalse
    have htrue := ih htrue
    funext x
    rw [← Fin.cons_self_tail x]
    cases x 0
    · exact congrFun hfalse (Fin.tail x)
    · exact congrFun htrue (Fin.tail x)

/-- Encode the number of variables as a unary word. -/
def unaryEncoding : ℕ ↪ List Bool :=
  ⟨Computability.unaryEncodingNat.encode, Computability.unaryEncodingNat.encode_injective⟩

/-- A single finite-state, binary multitape machine prints each truth table from $1^n$
in time at most $a(2^n)^k$, for fixed $a>0$ and $k$. Space is unrestricted. -/
def Explicit (f : BooleanFamily) : Prop :=
  ∃ a k : ℕ, 0 < a ∧ ∃ space,
    Turing.MultiTapeTM.ComputableInTimeAndSpace
      (fun n => truthTable (f n)) unaryEncoding (.refl _)
      (fun n => a * (2 ^ n) ^ k) space

/-- For all sufficiently large $n$, every $B_2$ circuit computing $f_n$ has at least
`bound n` gates. Comparing in $\mathbb{R}$ rounds a nonintegral lower bound upward. -/
def CircuitLowerBound (f : BooleanFamily) (bound : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ g (c : Circuit binarySignature n g 1),
    (∀ x, c.eval binaryInterpretation x 0 = f n x) → bound n ≤ g

end ComplexityTheory
