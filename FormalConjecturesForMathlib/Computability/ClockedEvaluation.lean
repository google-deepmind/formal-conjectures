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

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Explicit clocks and bounded transition semantics

A clock has the form $c(n+1)^k$, with $c>0$ and $k\geq 0$.
Execution counts applications of a supplied transition function to running states.
A halted state reached at the exact clock boundary succeeds. Timeout and invalid execution fail
the correctness check, for both possible reference answers.

This is a generic transition evaluator. A concrete program syntax, its encoding, and a simulation
in the repository's TM2 complexity model must be supplied before making runtime class claims.
-/

@[expose] public section

namespace Computability.ClockedEvaluation

/-- Explicit coefficient and exponent; zero coefficients are excluded. -/
structure Clock where
  coefficient : ℕ
  exponent : ℕ
  coefficient_pos : 0 < coefficient
  deriving DecidableEq

def Clock.bound (clock : Clock) (n : ℕ) : ℕ :=
  clock.coefficient * (n + 1) ^ clock.exponent

theorem Clock.bound_pos (clock : Clock) (n : ℕ) : 0 < clock.bound n :=
  Nat.mul_pos clock.coefficient_pos (Nat.pow_pos (by omega))

/-- Validate raw clock parameters without accepting a zero coefficient. -/
def Clock.ofNat (c k : ℕ) : Option Clock :=
  if h : 0 < c then some ⟨c, k, h⟩ else none

@[simp]
theorem Clock.ofNat_zero (k : ℕ) : Clock.ofNat 0 k = none := by simp [ofNat]

@[simp]
theorem Clock.ofNat_fields (clock : Clock) :
    Clock.ofNat clock.coefficient clock.exponent = some clock := by
  simp [ofNat, clock.coefficient_pos]

/-- Running states, halted outputs, and invalid configurations are distinct. -/
inductive State (σ : Type*) where
  | running : σ → State σ
  | halted : Bool → State σ
  | invalid : State σ
  deriving DecidableEq

inductive Outcome where
  | halted : Bool → Outcome
  | timeout : Outcome
  | invalid : Outcome
  deriving DecidableEq

variable {σ : Type*}

/-- Execute at most `fuel` transitions. Inspection of the final state consumes no transition. -/
def run (step : σ → State σ) : ℕ → State σ → Outcome
  | _, .halted b => .halted b
  | _, .invalid => .invalid
  | 0, .running _ => .timeout
  | n + 1, .running s => run step n (step s)

/-- Success requires an actual halted answer equal to the reference answer. -/
def Outcome.passes (outcome : Outcome) (expected : Bool) : Bool :=
  match outcome with
  | .halted b => b == expected
  | .timeout | .invalid => false

@[simp]
theorem Outcome.passes_eq_true (outcome : Outcome) (expected : Bool) :
    outcome.passes expected = true ↔ outcome = .halted expected := by
  cases outcome <;> simp [passes]

/-- Correctness within an explicit clock, parameterized by the input's declared size. -/
def checkWithin (step : σ → State σ) (clock : Clock) (size : ℕ)
    (initial : State σ) (expected : Bool) : Bool :=
  (run step (clock.bound size) initial).passes expected

theorem checkWithin_iff (step : σ → State σ) (clock : Clock) (size : ℕ)
    (initial : State σ) (expected : Bool) :
    checkWithin step clock size initial expected = true ↔
      run step (clock.bound size) initial = .halted expected := by
  simp [checkWithin]

end Computability.ClockedEvaluation
