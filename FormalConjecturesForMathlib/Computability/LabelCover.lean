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

public import FormalConjecturesForMathlib.Computability.PromiseProblems
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Count
public import Mathlib.Tactic.Linarith

/-!
# Explicit bipartite Label-Cover instances

Each edge has a left endpoint, a right endpoint, and a table for a total
projection on a fixed alphabet. The two vertex sets are disjoint copies of
Fin m, where m is the number of edges. Non-isolated vertices can be renamed
into this range; unused vertices have no effect on the satisfied-edge fraction.
Repeated endpoint pairs are rejected, so each bipartite edge has one constraint.

The fiber bound is at most d, with equal alphabets on both sides, following
Guruswami et al., *SDP gaps for 2-to-1 and other Label-Cover variants*,
Definitions 1–2 and Conjectures 1–2, pp.2–3:
https://www.cs.cmu.edu/~odonnell/papers/2-to-1-gaps.pdf.
For d=1, totality and equal finite alphabet sizes force a permutation.
The reference semantics use exhaustive finite quantification, not fast solvers.
-/

@[expose] public section

namespace Computability.LabelCover

/-- The endpoints lie in separate left and right vertex sets. -/
abbrev Edge := ℕ × ℕ × List ℕ

/-- An explicit list of constraints, all with equal weight. -/
abbrev Code := List Edge

/-- A total alphabet map with fibers of size at most d. -/
def Projection (d q : ℕ) (table : List ℕ) : Prop :=
  table.length = q ∧ (∀ j ∈ table, j < q) ∧
    ∀ j : Fin q, table.count j.val ≤ d

instance (d q : ℕ) (table : List ℕ) : Decidable (Projection d q table) := by
  unfold Projection
  infer_instance

/-- Nonempty, well-formed, unweighted bipartite projection games. -/
def Valid (d q : ℕ) (g : Code) : Prop :=
  0 < q ∧ 0 < g.length ∧ (g.map (fun e => (e.1, e.2.1))).Nodup ∧
    ∀ e ∈ g, e.1 < g.length ∧ e.2.1 < g.length ∧ Projection d q e.2.2

instance (d q : ℕ) (g : Code) : Decidable (Valid d q g) := by
  unfold Valid
  infer_instance

/-- Raw access is total; validity ensures the default case is never used. -/
def labelAt {m q : ℕ} (a : Fin m → Fin q) (i : ℕ) : ℕ :=
  if h : i < m then (a ⟨i, h⟩).val else 0

@[simp]
theorem labelAt_fin {m q : ℕ} (a : Fin m → Fin q) (i : Fin m) :
    labelAt a i.val = (a i).val := by
  simp [labelAt, i.isLt]

/-- A projection accepts exactly when the right label is the left label's image. -/
def accepts {m q : ℕ} (left right : Fin m → Fin q) (e : Edge) : Bool :=
  e.2.2[labelAt left e.1]? == some (labelAt right e.2.1)

/-- Number of satisfied edges, retaining every constraint once. -/
def satisfied (g : Code) {q : ℕ} (left right : Fin g.length → Fin q) : ℕ :=
  (g.filter (accepts left right)).length

theorem satisfied_le (g : Code) {q : ℕ} (left right : Fin g.length → Fin q) :
    satisfied g left right ≤ g.length := List.length_filter_le _ _

/-- Some labeling satisfies at least the indicated fraction. -/
def AtLeast (q : ℕ) (c : ℚ) (g : Code) : Prop :=
  ∃ left right : Fin g.length → Fin q, c * (g.length : ℚ) ≤ satisfied g left right

/-- Every labeling satisfies at most the indicated fraction. -/
def AtMost (q : ℕ) (s : ℚ) (g : Code) : Prop :=
  ∀ left right : Fin g.length → Fin q, (satisfied g left right : ℚ) ≤ s * g.length

instance (q : ℕ) (c : ℚ) (g : Code) : Decidable (AtLeast q c g) := by
  unfold AtLeast
  infer_instance

instance (q : ℕ) (s : ℚ) (g : Code) : Decidable (AtMost q s g) := by
  unfold AtMost
  infer_instance

def Yes (d q : ℕ) (c : ℚ) (g : Code) : Prop := Valid d q g ∧ AtLeast q c g

def No (d q : ℕ) (s : ℚ) (g : Code) : Prop := Valid d q g ∧ AtMost q s g

instance (d q : ℕ) (c : ℚ) (g : Code) : Decidable (Yes d q c g) := by
  unfold Yes
  infer_instance

instance (d q : ℕ) (s : ℚ) (g : Code) : Decidable (No d q s g) := by
  unfold No
  infer_instance

/-- The two promises do not overlap when soundness is below completeness. -/
theorem yes_not_no {d q : ℕ} {c s : ℚ} {g : Code} (hsc : s < c)
    (hy : Yes d q c g) : ¬ No d q s g := by
  intro hn
  obtain ⟨left, right, hc⟩ := hy.2
  have hs := hn.2 left right
  have hm : (0 : ℚ) < g.length := by exact_mod_cast hy.1.2.1
  nlinarith

/-- Perfect completeness is the existence of a labeling satisfying every edge. -/
theorem atLeast_one_iff (q : ℕ) (g : Code) :
    AtLeast q 1 g ↔ ∃ left right : Fin g.length → Fin q,
      satisfied g left right = g.length := by
  constructor
  · rintro ⟨left, right, h⟩
    have h' : g.length ≤ satisfied g left right := by
      exact_mod_cast (by simpa using h : (g.length : ℚ) ≤ satisfied g left right)
    exact ⟨left, right, Nat.le_antisymm (satisfied_le g left right) h'⟩
  · rintro ⟨left, right, h⟩
    exact ⟨left, right, by simp [h]⟩

end Computability.LabelCover
