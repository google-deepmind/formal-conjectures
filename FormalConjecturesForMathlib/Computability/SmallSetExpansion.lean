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

public import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import FormalConjecturesForMathlib.Computability.PromiseProblems
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith

/-!
# Small-set expansion on explicit regular graphs

We use the regular unweighted graph convention in Raghavendra–Steurer,
*Graph Expansion and the Unique Games Conjecture*, STOC 2010, pp.1–3,
Problem 1 and Conjecture 1.3: https://www.dsteurer.org/paper/expansion.pdf.

The input gives a loopless symmetric adjacency matrix and its positive degree.
A cut has exactly delta times the vertex count, not at most that size. Valid
inputs must admit a nonempty set of that exact size; this makes the implicit
integrality convention explicit. Each boundary edge is counted once, oriented
from inside to outside. Rational cross multiplication avoids rounding and
division by zero. This is not the weighted or irregular-graph variant.
-/

@[expose] public section

namespace Computability.SmallSetExpansion

open MatrixGraph

abbrev Input := Code × ℕ

/-- The number of adjacent vertices in an explicit matrix row. -/
def degree (g : Code) (i : Fin g.length) : ℕ :=
  (Finset.univ.filter (fun j => entry g i j = true)).card

/-- An oriented crossing pair counts one undirected boundary edge. -/
def boundary (g : Code) (s : Finset (Fin g.length)) : ℕ :=
  ((Finset.univ : Finset (Fin g.length × Fin g.length)).filter
    (fun p => p.1 ∈ s ∧ p.2 ∉ s ∧ entry g p.1 p.2 = true)).card

/-- Exact positive normalized size; no floor or ceiling is used. -/
def HasSize (δ : ℚ) (g : Code) (s : Finset (Fin g.length)) : Prop :=
  0 < s.card ∧ (s.card : ℚ) = δ * g.length

instance (δ : ℚ) (g : Code) (s : Finset (Fin g.length)) :
    Decidable (HasSize δ g s) := by
  unfold HasSize
  infer_instance

/-- Regularity, positive degree, and an attainable exact set size. -/
def Valid (δ : ℚ) (x : Input) : Prop :=
  ValidGraph x.1 ∧ 0 < x.2 ∧ (∀ i, degree x.1 i = x.2) ∧
    ∃ s : Finset (Fin x.1.length), HasSize δ x.1 s

instance (δ : ℚ) (x : Input) : Decidable (Valid δ x) := by
  unfold Valid
  infer_instance

/-- There is a set of the prescribed size with small edge expansion. -/
def Yes (η δ : ℚ) (x : Input) : Prop :=
  Valid δ x ∧ ∃ s : Finset (Fin x.1.length), HasSize δ x.1 s ∧
    (boundary x.1 s : ℚ) ≤ η * (x.2 * s.card : ℕ)

/-- All sets of the prescribed size have near-complete edge expansion. -/
def No (η δ : ℚ) (x : Input) : Prop :=
  Valid δ x ∧ ∀ s : Finset (Fin x.1.length), HasSize δ x.1 s →
    (1 - η) * (x.2 * s.card : ℕ) ≤ (boundary x.1 s : ℚ)

instance (η δ : ℚ) (x : Input) : Decidable (Yes η δ x) := by
  unfold Yes
  infer_instance

instance (η δ : ℚ) (x : Input) : Decidable (No η δ x) := by
  unfold No
  infer_instance

/-- The denominator in the source's expansion ratio is strictly positive. -/
theorem volume_pos {δ : ℚ} {x : Input} (hx : Valid δ x)
    {s : Finset (Fin x.1.length)} (hs : HasSize δ x.1 s) :
    (0 : ℚ) < (x.2 * s.card : ℕ) := by
  exact_mod_cast Nat.mul_pos hx.2.1 hs.1

/-- The stored inequality is exactly the source's conductance comparison. -/
theorem boundary_le_iff {δ η : ℚ} {x : Input} (hx : Valid δ x)
    {s : Finset (Fin x.1.length)} (hs : HasSize δ x.1 s) :
    (boundary x.1 s : ℚ) ≤ η * (x.2 * s.card : ℕ) ↔
      (boundary x.1 s : ℚ) / (x.2 * s.card : ℕ) ≤ η :=
  (div_le_iff₀ (volume_pos hx hs)).symm

theorem yes_not_no {η δ : ℚ} {x : Input} (hη : η < 1 / 2)
    (hy : Yes η δ x) : ¬ No η δ x := by
  intro hn
  obtain ⟨s, hs, hlow⟩ := hy.2
  have hhigh := hn.2 s hs
  have hpos := volume_pos hy.1 hs
  nlinarith

end Computability.SmallSetExpansion
