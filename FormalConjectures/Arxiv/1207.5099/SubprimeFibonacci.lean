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

public import FormalConjecturesUtil

/-!
# Conway's subprime Fibonacci sequences

A subprime Fibonacci sequence starts from two positive integers. Each new term is the sum of the
previous two terms if that sum is prime; if the sum is composite, it is divided once by its least
prime factor. This file formalizes the no-infinite-chains component of the conjecture: every such
sequence eventually enters a cycle. It does not assert that the seven known loops are complete or
unique.

*References:*
- R. K. Guy, T. Khovanova, and J. Salazar,
  ["Conway's subprime Fibonacci sequences"](https://arxiv.org/abs/1207.5099),
  *Mathematics Magazine* **87** (2014), no. 5, 323–337.
- [A214897](https://oeis.org/A214897), Conway's subprime Fibonacci sequence: cycle lengths.
-/

@[expose] public section

namespace Arxiv.«1207.5099»

/--
Conway's subprime function leaves a prime unchanged and divides a composite number once by its
least prime factor. It is extended by the identity on $0$ and $1$.
-/
def subprimePart (n : ℕ) : ℕ :=
  if n < 2 then n else if n.Prime then n else n / n.minFac

/--
One step of the subprime Fibonacci recurrence on a pair of consecutive terms. The second entry
becomes the first, and the subprime part of the sum becomes the second.
-/
def step (state : ℕ × ℕ) : ℕ × ℕ :=
  (state.2, subprimePart (state.1 + state.2))

/-- A pair state is eventually periodic if some positive iterate fixes a later state. -/
def EventuallyPeriodic (initial : ℕ × ℕ) : Prop :=
  ∃ preperiod period : ℕ, 0 < period ∧
    Function.IsPeriodicPt step period ((step^[preperiod]) initial)

/-- A prime sum passes unchanged to the next term. -/
@[category API, AMS 11]
theorem subprime_part_of_prime {n : ℕ} (hn : n.Prime) : subprimePart n = n := by
  simp [subprimePart, hn]

@[category test, AMS 11]
theorem subprime_part_zero : subprimePart 0 = 0 := by norm_num [subprimePart]

@[category test, AMS 11]
theorem subprime_part_one : subprimePart 1 = 1 := by norm_num [subprimePart]

@[category test, AMS 11]
theorem subprime_part_prime : subprimePart 13 = 13 := by norm_num [subprimePart]

@[category test, AMS 11]
theorem subprime_part_composite : subprimePart 12 = 6 := by norm_num [subprimePart]

@[category test, AMS 11]
theorem step_zero_one : step (0, 1) = (1, 1) := by norm_num [step, subprimePart]

@[category test, AMS 11]
theorem one_one_not_fixed_point : ¬ Function.IsFixedPt step (1, 1) := by
  norm_num [Function.IsFixedPt, step, subprimePart]

/-- The example from the paper begins $0,1,1,2,3,5,4,3,7$. -/
@[category test, AMS 11]
theorem zero_one_after_seven_steps : (step^[7]) (0, 1) = (3, 7) := by
  norm_num [Function.iterate_succ_apply, step, subprimePart]

/-- The pair $(2,2)$ is the cycle of length one. -/
@[category test, AMS 11]
theorem two_two_fixed_point : Function.IsFixedPt step (2, 2) := by
  norm_num [Function.IsFixedPt, step, subprimePart]

@[category test, AMS 11]
theorem two_two_eventually_periodic : EventuallyPeriodic (2, 2) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  simpa [Function.IsPeriodicPt] using two_two_fixed_point

/-- An 18-step return along the paper's nontrivial cycle through $(13,61)$. -/
@[category test, AMS 11]
theorem thirteen_sixty_one_periodic : (step^[18]) (13, 61) = (13, 61) := by
  norm_num [Function.iterate_succ_apply, step, subprimePart]

/--
Every subprime Fibonacci sequence starting from two positive integers eventually enters a cycle.
This is the "no infinite chains" conjecture recorded in [A214897](https://oeis.org/A214897),
associated with [Guy–Khovanova–Salazar](https://arxiv.org/abs/1207.5099).
-/
@[category research open, AMS 11]
theorem conjecture (x y : ℕ) (hx : 0 < x) (hy : 0 < y) : EventuallyPeriodic (x, y) := by
  sorry

end Arxiv.«1207.5099»
