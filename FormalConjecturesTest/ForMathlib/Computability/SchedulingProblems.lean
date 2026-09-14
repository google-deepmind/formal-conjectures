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
import FormalConjecturesForMathlib.Computability.DecisionProblems
import FormalConjecturesForMathlib.Computability.SchedulingProblems

/-! # Kernel-checked scheduling and packing boundary cases -/

namespace Computability.SchedulingProblems.Test

-- Endpoints may touch. A zero-duration interval occupies no resource.
example : Separated 0 2 2 3 := by decide
example : Separated 2 3 0 2 := by decide
example : ¬ Separated 0 2 1 2 := by decide
example : ¬ Separated 1 2 1 2 := by decide
example : Separated 0 5 2 0 := by decide
example : Separated 2 0 0 5 := by decide
example : Separated 2 0 2 0 := by decide
example : Disjoint (Finset.Ico 0 5) (Finset.Ico 2 2) :=
  (separated_iff_disjoint 0 5 2 0).mp (by decide)

-- Finite starts include the deadline itself for zero-duration operations.
example : FeasibleBy (fun _ : Fin 1 ↦ 2) (fun _ ↦ 0) (fun s ↦ s 0 = 2) := by decide
example : ¬ FeasibleBy (fun _ : Fin 1 ↦ 2) (fun _ ↦ 1) (fun s ↦ s 0 = 2) := by decide
example : FeasibleBy (fun _ : Fin 1 ↦ 0) (fun _ ↦ 0) (fun _ ↦ True) := by decide
example : FeasibleBy (fun _ : Fin 0 ↦ 0) (fun _ ↦ 1) (fun _ ↦ True) := by decide

-- Indexed items preserve multiplicity, and bin capacity is not just a total-size test.
example : BinPacking ([], 1, 1) := by decide
example : BinPacking ([1], 1, 3) := by decide
example : BinPacking ([2, 2], 2, 2) := by decide
example : ¬ BinPacking ([2, 2], 2, 1) := by decide
example : BinPacking ([1, 2, 3], 3, 2) := by decide
example : ¬ BinPacking ([2, 2, 2], 3, 2) := by decide
example : ¬ BinPacking ([4], 3, 2) := by decide
example : ¬ BinPacking ([0], 1, 1) := by decide
example : ¬ BinPacking ([], 0, 1) := by decide
example : ¬ BinPacking ([], 1, 0) := by decide

-- Individual windows, idle time, strict positivity, and inclusive completion deadlines.
example : ReleaseDeadline [] := by decide
example : ReleaseDeadline [(1, 0, 1)] := by decide
example : ReleaseDeadline [(1, 2, 3)] := by decide
example : ¬ ReleaseDeadline [(1, 2, 2)] := by decide
example : ¬ ReleaseDeadline [(1, 3, 2)] := by decide
example : ¬ ReleaseDeadline [(0, 0, 1)] := by decide
example : ¬ ReleaseDeadline [(1, 0, 0)] := by decide
example : ReleaseDeadline [(1, 0, 2), (1, 0, 2)] := by decide
example : ¬ ReleaseDeadline [(1, 0, 1), (1, 0, 1)] := by decide
example : ReleaseDeadline [(1, 0, 1), (1, 2, 3)] := by decide
-- The long task fits only if split around [1,2); our nonpreemptive model rejects it.
example : ¬ ReleaseDeadline [(3, 0, 4), (1, 1, 2)] := by decide

-- Rectangular dimensions and strictly positive machine/deadline parameters.
example : OpenShop (1, [], 1) := by decide
example : FlowShop (1, [], 1) := by decide
example : ¬ OpenShop (0, [], 1) := by decide
example : ¬ OpenShop (1, [], 0) := by decide
example : ¬ OpenShop (2, [[1]], 1) := by decide
example : ¬ OpenShop (1, [[1, 1]], 1) := by decide
example : ¬ OpenShop (1, [[]], 1) := by decide
example : ¬ FlowShop (2, [[1]], 1) := by decide
example : ¬ FlowShop (0, [], 1) := by decide
example : ¬ FlowShop (1, [], 0) := by decide

-- Open shop has both machine and job resource constraints, even without precedence.
example : OpenShop (1, [[1]], 1) := by decide
example : OpenShop (2, [[0, 0]], 1) := by decide
example : FlowShop (2, [[0, 0]], 1) := by decide
example : ¬ OpenShop (1, [[2]], 1) := by decide
example : ¬ OpenShop (1, [[1], [1]], 1) := by decide
example : OpenShop (1, [[1], [1]], 2) := by decide
example : ¬ OpenShop (2, [[2, 2]], 2) := by decide
example : OpenShop (2, [[1, 1], [1, 1]], 2) := by decide
example : ¬ FlowShop (2, [[1, 1], [1, 1]], 2) := by decide
example : FlowShop (2, [[1, 1], [1, 1]], 3) := by decide
example : FlowShop (2, [[1, 0]], 1) := by decide
example : FlowShop (2, [[0, 1]], 1) := by decide

-- A concrete flow schedule with different job orders on the two machines.
abbrev waitingShop : ShopInput := (2, [[1, 1], [1, 1]], 5)

def waitingStart (o : ShopOperation waitingShop) : ℕ :=
  if o.1.val = 0 then (if o.2.val = 0 then 0 else 4)
  else (if o.2.val = 0 then 1 else 2)

example : ShopResources waitingShop waitingStart := by decide
example : FlowOrder waitingShop waitingStart := by decide
example : ∀ o, waitingStart o + shopLength waitingShop o ≤ 5 := by decide
example : waitingStart (0, 0) < waitingStart (1, 0) ∧
    waitingStart (1, 1) < waitingStart (0, 1) := by decide
example : waitingStart (0, 0) + shopLength waitingShop (0, 0) <
    waitingStart (0, 1) := by decide

-- Empty global job lists are allowed, but every listed job must contain an operation.
example : JobShop (1, [], 1) := by decide
example : ¬ JobShop (0, [], 1) := by decide
example : ¬ JobShop (1, [], 0) := by decide
example : ¬ JobShop (1, [[]], 1) := by decide
example : ¬ JobShop (1, [[(1, 0)]], 1) := by decide
example : JobShop (1, [[(0, 0)]], 1) := by decide
example : JobShop (1, [[(0, 1)]], 1) := by decide
example : ¬ JobShop (1, [[(0, 2)]], 1) := by decide
example : ¬ JobShop (1, [[(0, 1)], [(0, 1)]], 1) := by decide
example : JobShop (1, [[(0, 1)], [(0, 1)]], 2) := by decide
example : JobShop (2, [[(0, 1)], [(1, 1)]], 1) := by decide
example : ¬ JobShop (2, [[(0, 1), (1, 1)]], 1) := by decide
example : JobShop (2, [[(0, 1), (1, 1)]], 2) := by decide
example : JobShop (2, [[(0, 1), (1, 1)], [(1, 1), (0, 1)]], 2) := by decide
example : JobShop (2, [[(0, 1), (1, 1), (0, 1)]], 3) := by decide
example : ¬ JobShop (2, [[(0, 1), (0, 1)]], 2) := by decide
example : ¬ JobShop (2, [[(0, 0), (0, 0)]], 1) := by decide
example : JobShop (2, [[(0, 1), (1, 0)]], 1) := by decide
example : JobShop (2, [[(0, 0), (1, 1)]], 1) := by decide
example : JobShop (2, [[(0, 1)], [(1, 0), (0, 0)]], 1) := by decide

-- Zero-duration operations may occur within another operation's processing interval.
abbrev zeroShop : ShopInput := (1, [[3], [0]], 3)

def zeroStart (o : ShopOperation zeroShop) : ℕ :=
  if o.1.val = 0 then 0 else 1

example : ShopResources zeroShop zeroStart := by decide
example : FlowOrder zeroShop zeroStart := by decide
example : ∀ o, zeroStart o + shopLength zeroShop o ≤ 3 := by decide

-- A zero-length stage is still subject to the job's precedence constraint.
abbrev zeroChain : JobShopInput := (2, [[(0, 1), (1, 0)]], 1)

example : ¬ JobConstraints zeroChain (fun _ ↦ 0) := by decide
example : JobConstraints zeroChain (fun o ↦ o.2.val) := by decide

-- The predicate has a genuine encoded-machine interface, independent of exhaustive tests.
example : BitstringEncoding PackingInput := inferInstance
example : BitstringEncoding WindowInput := inferInstance
example : BitstringEncoding ShopInput := inferInstance
example : BitstringEncoding JobShopInput := inferInstance

theorem nonvacuous_machine_interface :
    ComplexityTheory.HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

open BitstringEncoding in
example : bitDecode (bitEncode (([1, 2, 3], 3, 2) : PackingInput)) =
    some (([1, 2, 3], 3, 2) : PackingInput) := bitDecode_bitEncode _

open BitstringEncoding in
example : bitDecode (bitEncode ([(3, 0, 4), (1, 1, 2)] : WindowInput)) =
    some ([(3, 0, 4), (1, 1, 2)] : WindowInput) := bitDecode_bitEncode _

open BitstringEncoding in
example : bitDecode (bitEncode waitingShop) = some waitingShop := bitDecode_bitEncode _

open BitstringEncoding in
example : bitDecode (bitEncode zeroChain) = some zeroChain := bitDecode_bitEncode _

/-- info: true -/
#guard_msgs in
#eval decide (OpenShop (2, [[1, 1], [1, 1]], 2))

/-- info: false -/
#guard_msgs in
#eval decide (ReleaseDeadline [(3, 0, 4), (1, 1, 2)])

end Computability.SchedulingProblems.Test
