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

public import FormalConjecturesForMathlib.Computability.EncodedBooleanCircuit
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi

/-!
# End-of-Line and Circuit-FLIP search

End-of-Line uses successor and predecessor circuits, including both kinds of
allowed answer. In particular, zero is allowed as an answer when P(S(0)) ≠ 0.
The distinguished source is excluded only from the second kind of answer.

Circuit-FLIP asks for any local minimum, not the endpoint reached by a prescribed
improvement trajectory. Output bits have little-endian weights starting at two,
as in the source's sum from j = 1 of 2^j times the jth output bit.

References:
* Ghentiyala–Li, *Hierarchies within TFNP: building blocks and collapses*,
  ECCC TR25-123 revision1, Definition2.8, printed p.8:
  https://eccc.weizmann.ac.il/report/2025/123/revision/1/download.
* Johnson–Papadimitriou–Yannakakis, *How Easy Is Local Search?* (1988),
  §3, Theorem1, pp.86–87, https://doi.org/10.1016/0022-0000(88)90046-3.

The totality proofs are ambient finite arguments, not polynomial-time algorithms
or formal completeness reductions to the repository's complexity classes.
-/

@[expose] public section

namespace TotalSearch

open EncodedBooleanCircuit

def assignment (n : ℕ) (bs : List Bool) : Fin n → Bool := fun i => bs[i.val]?.getD false

@[simp] theorem assignment_ofFn {n : ℕ} (v : Fin n → Bool) :
    assignment n (List.ofFn v) = v := by
  funext i
  simp [assignment]

@[simp] theorem ofFn_assignment (bs : List Bool) :
    List.ofFn (assignment bs.length bs) = bs := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i hi hj
    simp only [List.getElem_ofFn, assignment, List.getElem?_eq_getElem hj, Option.getD_some]

def evalAssignment {n : ℕ} (c : Circuit) (v : Fin n → Bool) : Fin n → Bool :=
  assignment n (eval c (List.ofFn v))

theorem ofFn_evalAssignment {n : ℕ} (c : Circuit) (v : Fin n → Bool)
    (h : c.2.2.length = n) :
    List.ofFn (evalAssignment c v) = eval c (List.ofFn v) := by
  have hl : (eval c (List.ofFn v)).length = n := (length_eval c _).trans h
  apply List.ext_getElem
  · simpa using hl.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, evalAssignment, assignment,
      List.getElem?_eq_getElem hj, Option.getD_some]

abbrev EndOfLineInput := Circuit × Circuit

def EndOfLinePromise (c : EndOfLineInput) : Prop :=
  Valid c.1 ∧ Valid c.2 ∧ arity c.2 = arity c.1 ∧
    c.1.2.2.length = arity c.1 ∧ c.2.2.2.length = arity c.1 ∧
    evalAssignment (n := arity c.1) c.2 (fun _ => false) = (fun _ => false) ∧
    evalAssignment (n := arity c.1) c.1 (fun _ => false) ≠ (fun _ => false)

instance (c : EndOfLineInput) : Decidable (EndOfLinePromise c) := by
  unfold EndOfLinePromise
  infer_instance

def EndOfLineSolution (c : EndOfLineInput) (bs : List Bool) : Prop :=
  bs.length = arity c.1 ∧
    let v := assignment (arity c.1) bs
    evalAssignment c.2 (evalAssignment c.1 v) ≠ v ∨
      (v ≠ (fun _ => false) ∧ evalAssignment c.1 (evalAssignment c.2 v) ≠ v)

instance (c : EndOfLineInput) (bs : List Bool) : Decidable (EndOfLineSolution c bs) := by
  unfold EndOfLineSolution
  infer_instance

/-- The finite injectivity/surjectivity argument underlying a directed endpoint. -/
theorem endpoint_exists {α : Type*} [Finite α] (s p : α → α) (z : α)
    (hp : p z = z) (hs : s z ≠ z) : ∃ x, p (s x) ≠ x := by
  classical
  by_contra h
  have hl : Function.LeftInverse p s := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := (Finite.surjective_of_injective hl.injective) z
  have he : x = z := by rw [← hl x, hx, hp]
  exact hs (by simpa [he] using hx)

theorem endOfLine_total (c : EndOfLineInput) (hc : EndOfLinePromise c) :
    ∃ bs, EndOfLineSolution c bs := by
  obtain ⟨v, hv⟩ := endpoint_exists
    (evalAssignment (n := arity c.1) c.1) (evalAssignment c.2) (fun _ => false)
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  refine ⟨List.ofFn v, List.length_ofFn, ?_⟩
  simp only [assignment_ofFn]
  exact Or.inl hv

def flip {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update v i (!(v i))

@[simp] theorem flip_same {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    flip v i i = !(v i) := by simp [flip]

theorem flip_other {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flip v i j = v j := by simp [flip, h]

@[simp] theorem flip_twice {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    flip (flip v i) i = v := by
  funext j
  by_cases h : j = i <;> simp [flip, h]

/-- Ordinary little-endian binary value, including noncanonical trailing zeros. -/
def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitValue bs

theorem bitValue_lt (bs : List Bool) : bitValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitValue]
  | cons b bs ih =>
    cases b <;> simp only [bitValue, Bool.toNat_false, Bool.toNat_true,
      List.length_cons, pow_succ] <;> omega

@[simp] theorem bitValue_append_false (bs : List Bool) :
    bitValue (bs ++ [false]) = bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, bitValue, ih]

/-- The source numbers outputs from one, giving the first bit weight two. -/
def cost {n : ℕ} (c : Circuit) (v : Fin n → Bool) : ℕ :=
  2 * bitValue (eval c (List.ofFn v))

theorem cost_le_iff {n : ℕ} (c : Circuit) (v w : Fin n → Bool) :
    cost c v ≤ cost c w ↔
      bitValue (eval c (List.ofFn v)) ≤ bitValue (eval c (List.ofFn w)) := by
  unfold cost
  omega

def FlipSolution (c : Circuit) (bs : List Bool) : Prop :=
  bs.length = arity c ∧ ∀ i : Fin (arity c),
    cost c (assignment (arity c) bs) ≤ cost c (flip (assignment (arity c) bs) i)

instance (c : Circuit) (bs : List Bool) : Decidable (FlipSolution c bs) := by
  unfold FlipSolution
  infer_instance

theorem flip_total (c : Circuit) : ∃ bs, FlipSolution c bs := by
  obtain ⟨v, _, hv⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin (arity c) → Bool)) (cost c) Finset.univ_nonempty
  refine ⟨List.ofFn v, List.length_ofFn, ?_⟩
  simp only [assignment_ofFn]
  exact fun i => hv (flip v i) (Finset.mem_univ _)

end TotalSearch
