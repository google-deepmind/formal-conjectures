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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite packing and nonpreemptive scheduling problems

Inputs use lists and natural-number data, so the existing list/pair binary encodings apply.
List positions distinguish items, jobs, and operations even when their data agree.

Reference: Garey and Johnson, *Computers and Intractability* (1979), SR1 (p. 226),
SS1 (p. 236), SS14–SS15 (p. 241), SS18 (p. 242).
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Schedules assign one integer start to each operation. Resource use is a half-open interval;
a zero-duration operation occupies no resource but still obeys precedence constraints.
This agrees with the nonpreemptive processing model of Gonzalez and Sahni,
*Open Shop Scheduling to Minimize Finish Time* (1976), pp. 665–666.
https://doi.org/10.1145/321978.321985
It differs from the literal machine-order clauses of Garey–Johnson SS14/SS15/SS18:
a zero-duration operation may start strictly inside another operation's busy interval.

The finite witness bounds below are equivalent to unrestricted natural-number start times.
Exhaustive decidability is not a polynomial-time algorithm claim.
-/

@[expose] public section

namespace Computability.SchedulingProblems

open Finset

/-- Two half-open processing intervals do not overlap. Zero-duration operations are empty,
even when their start lies inside another operation's busy interval. This is the processing-
interval convention, not Garey–Johnson's literal machine-order clause for zero-length tasks. -/
def Separated (s p t q : ℕ) : Prop :=
  p = 0 ∨ q = 0 ∨ s + p ≤ t ∨ t + q ≤ s

instance (s p t q : ℕ) : Decidable (Separated s p t q) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem separated_iff_disjoint (s p t q : ℕ) :
    Separated s p t q ↔ Disjoint (Ico s (s + p)) (Ico t (t + q)) := by
  rw [Finset.disjoint_left]
  simp only [Finset.mem_Ico]
  constructor
  · intro h x hx hy
    unfold Separated at h
    omega
  · intro h
    by_contra hn
    have hp : 0 < p := by unfold Separated at hn; omega
    have hq : 0 < q := by unfold Separated at hn; omega
    have hst : t < s + p := by unfold Separated at hn; omega
    have hts : s < t + q := by unfold Separated at hn; omega
    exact h (by omega : s ≤ max s t ∧ max s t < s + p)
      (by omega : t ≤ max s t ∧ max s t < t + q)

theorem separated_comm (s p t q : ℕ) :
    Separated s p t q ↔ Separated t q s p := by
  unfold Separated
  omega

/-- With positive lengths, separation is the usual disjunction of execution orders. -/
theorem separated_iff_of_pos {s p t q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Separated s p t q ↔ s + p ≤ t ∨ t + q ≤ s := by
  unfold Separated
  omega

/-- A finite start-time witness, bounded by an operation-specific completion deadline. -/
def FeasibleBy {α : Type} (deadline length : α → ℕ)
    (constraints : (α → ℕ) → Prop) : Prop :=
  ∃ start : (i : α) → Fin (deadline i + 1),
    (∀ i, (start i).val + length i ≤ deadline i) ∧ constraints (fun i ↦ (start i).val)

instance {α : Type} [Fintype α] [DecidableEq α] (deadline length : α → ℕ)
    (constraints : (α → ℕ) → Prop) [DecidablePred constraints] :
    Decidable (FeasibleBy deadline length constraints) :=
  inferInstanceAs (Decidable (∃ _ : (i : α) → Fin (deadline i + 1), _))

/-- Completion bounds justify finite starts, including a zero-length start at the deadline. -/
theorem feasibleBy_iff {α : Type} (deadline length : α → ℕ)
    (constraints : (α → ℕ) → Prop) :
    FeasibleBy deadline length constraints ↔
      ∃ start : α → ℕ, (∀ i, start i + length i ≤ deadline i) ∧ constraints start := by
  constructor
  · rintro ⟨start, hfinish, hc⟩
    exact ⟨fun i ↦ (start i).val, hfinish, hc⟩
  · rintro ⟨start, hfinish, hc⟩
    exact ⟨fun i ↦ ⟨start i, by have := hfinish i; omega⟩, hfinish, hc⟩

/-- Completion times along a nonnegative-length job chain are nondecreasing. -/
theorem chain_completion_monotone {n : ℕ} (start length : Fin n → ℕ)
    (h : ∀ a b : Fin n, a.val + 1 = b.val → start a + length a ≤ start b) :
    Monotone (fun i ↦ start i + length i) := by
  cases n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have := h i.castSucc i.succ rfl
    omega

/-- For a nonempty job chain, bounding the last completion bounds every completion. -/
theorem chain_completion_iff_last {n : ℕ} (start length : Fin (n + 1) → ℕ) (D : ℕ)
    (h : ∀ a b : Fin (n + 1), a.val + 1 = b.val → start a + length a ≤ start b) :
    (∀ i, start i + length i ≤ D) ↔ start (Fin.last n) + length (Fin.last n) ≤ D := by
  constructor
  · exact fun hall ↦ hall (Fin.last n)
  · intro hlast i
    exact (chain_completion_monotone start length h (Fin.le_last i)).trans hlast

/-- Item sizes, bin capacity, and number of available bins. -/
abbrev PackingInput := List ℕ × ℕ × ℕ

/-- SR1. Every indexed item is assigned exactly once; unused bins are allowed. -/
def BinPacking (x : PackingInput) : Prop :=
  (∀ i : Fin x.1.length, 0 < x.1[i]) ∧ 0 < x.2.1 ∧ 0 < x.2.2 ∧
    ∃ bin : Fin x.1.length → Fin x.2.2,
      ∀ b, (∑ i : Fin x.1.length, if bin i = b then x.1[i] else 0) ≤ x.2.1

instance (x : PackingInput) : Decidable (BinPacking x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∃ _ : Fin x.1.length → Fin x.2.2, _))

/-- Each row records processing length, release time, and individual deadline. -/
abbrev WindowInput := List (ℕ × ℕ × ℕ)

/-- Release-time and single-machine constraints; completion bounds are supplied separately. -/
def WindowConstraints (jobs : WindowInput) (start : Fin jobs.length → ℕ) : Prop :=
  (∀ i, jobs[i].2.1 ≤ start i) ∧
    ∀ i j, i ≠ j → Separated (start i) jobs[i].1 (start j) jobs[j].1

instance (jobs : WindowInput) (start : Fin jobs.length → ℕ) :
    Decidable (WindowConstraints jobs start) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ _, _))

/-- SS1. Positive task lengths and deadlines, nonnegative releases, and no preemption. -/
def ReleaseDeadline (jobs : WindowInput) : Prop :=
  (∀ i : Fin jobs.length, 0 < jobs[i].1 ∧ 0 < jobs[i].2.2) ∧
    FeasibleBy (fun i ↦ jobs[i].2.2) (fun i ↦ jobs[i].1) (WindowConstraints jobs)

instance (jobs : WindowInput) : Decidable (ReleaseDeadline jobs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Positive tasks in a one-machine schedule cannot have equal starts. -/
theorem WindowConstraints.injective {jobs : WindowInput} {start : Fin jobs.length → ℕ}
    (h : WindowConstraints jobs start) (hp : ∀ i : Fin jobs.length, 0 < jobs[i].1) :
    Function.Injective start := by
  intro i j hij
  by_contra hne
  have hs := h.2 i j hne
  have hi := hp i
  have hj := hp j
  unfold Separated at hs
  omega

/-- Processor count, one row of processing lengths per job, and overall deadline. -/
abbrev ShopInput := ℕ × List (List ℕ) × ℕ

/-- A rectangular shop has one operation for every job/machine pair. -/
abbrev ShopOperation (x : ShopInput) := Fin x.2.1.length × Fin x.1

/-- The length of the operation on the designated machine; shape checks exclude missing entries. -/
def shopLength (x : ShopInput) (o : ShopOperation x) : ℕ :=
  x.2.1[o.1][o.2.val]?.getD 0

/-- Positive processor count and deadline, with exactly one duration per machine in each row. -/
def ShopShape (x : ShopInput) : Prop :=
  0 < x.1 ∧ 0 < x.2.2 ∧ ∀ j : Fin x.2.1.length, x.2.1[j].length = x.1

instance (x : ShopInput) : Decidable (ShopShape x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _, _))

/-- On valid input, length lookup uses an actual entry, never the default value. -/
theorem shopLength_eq_get {x : ShopInput} (h : ShopShape x) (o : ShopOperation x) :
    shopLength x o = x.2.1[o.1][o.2.val]'(by rw [h.2.2 o.1]; exact o.2.isLt) := by
  simp only [shopLength, List.getElem?_eq_getElem (by rw [h.2.2 o.1]; exact o.2.isLt),
    Option.getD_some]

/-- Neither a machine nor a job can participate in two positive-length operations at once. -/
def ShopResources (x : ShopInput) (start : ShopOperation x → ℕ) : Prop :=
  ∀ u v, u ≠ v → (u.1 = v.1 ∨ u.2 = v.2) →
    Separated (start u) (shopLength x u) (start v) (shopLength x v)

instance (x : ShopInput) (start : ShopOperation x → ℕ) :
    Decidable (ShopResources x start) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- Every job visits machines in their listed order; waiting between stages is allowed. -/
def FlowOrder (x : ShopInput) (start : ShopOperation x → ℕ) : Prop :=
  ∀ j : Fin x.2.1.length, ∀ a b : Fin x.1, a.val + 1 = b.val →
    start (j, a) + shopLength x (j, a) ≤ start (j, b)

instance (x : ShopInput) (start : ShopOperation x → ℕ) :
    Decidable (FlowOrder x start) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- SS14. Nonpreemptive open shop, with no prescribed operation order within each job. -/
def OpenShop (x : ShopInput) : Prop :=
  ShopShape x ∧ FeasibleBy (fun _ ↦ x.2.2) (shopLength x) (ShopResources x)

instance (x : ShopInput) : Decidable (OpenShop x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- SS15. Nonpreemptive flow shop, without a common job-order requirement across machines. -/
def FlowShop (x : ShopInput) : Prop :=
  ShopShape x ∧ FeasibleBy (fun _ ↦ x.2.2) (shopLength x)
    (fun start ↦ ShopResources x start ∧ FlowOrder x start)

instance (x : ShopInput) : Decidable (FlowShop x) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem FlowShop.openShop {x : ShopInput} (h : FlowShop x) : OpenShop x := by
  rcases h with ⟨hshape, start, hfinish, hresource, _⟩
  exact ⟨hshape, start, hfinish, hresource⟩

/-- Processor count, ordered jobs of (zero-based machine, duration) pairs, and deadline. -/
abbrev JobShopInput := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- Only actual operation positions occur, even when job lengths differ. -/
abbrev JobOperation (x : JobShopInput) :=
  (j : Fin x.2.1.length) × Fin x.2.1[j].length

/-- The machine and duration of an indexed job-shop operation. -/
def jobTask (x : JobShopInput) (o : JobOperation x) : ℕ × ℕ :=
  x.2.1[o.1][o.2]

/-- SS18 input conventions. Jobs are nonempty; consecutive machines differ.
Nonconsecutive visits to the same machine are allowed. -/
def JobShopShape (x : JobShopInput) : Prop :=
  0 < x.1 ∧ 0 < x.2.2 ∧
    (∀ j : Fin x.2.1.length, 0 < x.2.1[j].length) ∧
    (∀ o : JobOperation x, (jobTask x o).1 < x.1) ∧
    ∀ j : Fin x.2.1.length, ∀ a b : Fin x.2.1[j].length, a.val + 1 = b.val →
      (jobTask x ⟨j, a⟩).1 ≠ (jobTask x ⟨j, b⟩).1

instance (x : JobShopInput) : Decidable (JobShopShape x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ ∀ _ _ _, _))

/-- Machine capacity and the consecutive operation order in every job. -/
def JobConstraints (x : JobShopInput) (start : JobOperation x → ℕ) : Prop :=
  (∀ u v, u ≠ v → (jobTask x u).1 = (jobTask x v).1 →
    Separated (start u) (jobTask x u).2 (start v) (jobTask x v).2) ∧
    ∀ j : Fin x.2.1.length, ∀ a b : Fin x.2.1[j].length, a.val + 1 = b.val →
      start ⟨j, a⟩ + (jobTask x ⟨j, a⟩).2 ≤ start ⟨j, b⟩

instance (x : JobShopInput) (start : JobOperation x → ℕ) :
    Decidable (JobConstraints x start) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ _ _, _))

/-- The source's last-operation deadline and the all-operation bound agree on job chains. -/
theorem JobConstraints.completion_iff_last {x : JobShopInput}
    {start : JobOperation x → ℕ} (h : JobConstraints x start) (D : ℕ) :
    (∀ o, start o + (jobTask x o).2 ≤ D) ↔
      ∀ j : Fin x.2.1.length, ∀ last : Fin x.2.1[j].length,
        last.val + 1 = x.2.1[j].length → start ⟨j, last⟩ + (jobTask x ⟨j, last⟩).2 ≤ D := by
  constructor
  · exact fun hall j last _ ↦ hall ⟨j, last⟩
  · intro hlast o
    have ho := o.2.isLt
    have hn : 0 < x.2.1[o.1].length := by omega
    let last : Fin x.2.1[o.1].length := ⟨x.2.1[o.1].length - 1, by omega⟩
    have hm := chain_completion_monotone (fun i ↦ start ⟨o.1, i⟩)
      (fun i ↦ (jobTask x ⟨o.1, i⟩).2) (h.2 o.1)
    exact (hm (show o.2 ≤ last by
      change o.2.val ≤ x.2.1[o.1].length - 1
      omega)).trans (hlast o.1 last (by
        change x.2.1[o.1].length - 1 + 1 = x.2.1[o.1].length
        omega))

/-- SS18. All operations meet the overall deadline, without preemption.
With the job chains this is equivalent to bounding each last operation's completion. -/
def JobShop (x : JobShopInput) : Prop :=
  JobShopShape x ∧
    FeasibleBy (fun _ ↦ x.2.2) (fun o ↦ (jobTask x o).2) (JobConstraints x)

instance (x : JobShopInput) : Decidable (JobShop x) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Computability.SchedulingProblems
