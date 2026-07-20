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

import FormalConjecturesUtil
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Basic

/-!
# Erdős Problem 769

*Reference:* [erdosproblems.com/769](https://www.erdosproblems.com/769)

Let $c(n)$ be minimal such that if $k\ge c(n)$ then the $n$-dimensional unit cube
can be decomposed into $k$ homothetic $n$-dimensional cubes.
Give good bounds for $c(n)$ – in particular, is it true that $c(n) \gg n^n$?
-/

namespace Erdos769

open Set Real Filter Asymptotics

/--
The $n$-dimensional unit cube $[0,1]^n$.
-/
def unit cube: $aCube (n : ℕ) : Set (Fin n → ℝ) := { x : Fin n → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1 }

/--
A homothetic copy of the unit + s \cdot [0,1]^n$, where $s > 0$ and $a \in \mathbb R^n$.
-/
def homotheticCube (n : ℕ) (a : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) :=
  if s > 0 then { x | ∀ i, a i ≤ x i ∧ x i ≤ a i + s } else ∅

/--
A set is a homothetic cube (positive scale).
-/
def isHomotheticCube (n : ℕ) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ a : Fin n → ℝ, ∃ s : ℝ, s > 0 ∧ C = homotheticCube n a s

/--
A set of cubes forms a decomposition of the unit cube if:
- all are homothetic copies (positive scale),
- their interiors are pairwise disjoint,
- their union is the unit cube.
-/
def isDecomposition (n : ℕ) (cubes : Finset (Set (Fin n → ℝ))) : Prop :=
  (∀ C ∈ cubes, isHomotheticCube n C) ∧
  (∀ C1 ∈ cubes, ∀ C2 ∈ cubes, C1 ≠ C2 → interior C1 ∩ interior C2 = ∅) ∧
  (⋃ C ∈ cubes, C) = unitCube n

/--
Predicate: the $n$-dimensional unit cube can be decomposed into exactly `k` homothetic cubes.
-/
def decomposable (n k : ℕ) : Prop :=
  ∃ cubes : Finset (Set (Fin n → ℝ)), cubes.card = k ∧ isDecomposition n cubes

/--
The minimal threshold $c(n)$: the smallest natural number `c` such that for every `k ≥ c`,
the unit cube can be decomposed into `k` homothetic cubes.
If no such `c` exists (for theoretical reasons), we set it to 0 (but in practice it is assumed to exist).
-/
noncomputable def c (n : ℕ) : ℕ :=
  let S := { k : ℕ | ∀ m ≥ k, decomposable n m }
  if S.Nonempty then sInf S else 0

/--
Conjecture: $c(n)$ grows faster than $n^n$, i.e. $n^n = o(c(n))$.
-/
@[category research open, AMS 52]
theorem erdos_769 : (fun n => (n : ℝ)^n) =o[atTop] (fun n => (c n : ℝ)) := by
  sorry

-- TODO(firsching): formalize other results from the additional material

end Erdos769
