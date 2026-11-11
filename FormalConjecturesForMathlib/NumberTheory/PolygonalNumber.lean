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

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Triangular, polygonal, and generalized polygonal numbers

This file defines triangular numbers, the `Nat.IsTriangular` predicate, $m$-gonal numbers
`Nat.polygonalNumber m x`, and generalized $m$-gonal numbers `Nat.generalizedPolygonalNumber m k`
for $k \in \mathbb{Z}$.
-/

@[expose] public section

namespace Nat

/-- The $n$-th triangular number $T_n = n(n + 1) / 2$. -/
def triangular (n : ℕ) : ℕ :=
  n * (n + 1) / 2

@[simp]
theorem triangular_zero : triangular 0 = 0 := rfl

@[simp]
theorem triangular_one : triangular 1 = 1 := rfl

/-- Predicate stating that $n$ is a triangular number $k(k + 1) / 2$ for some $k \in \mathbb{N}$. -/
def IsTriangular (n : ℕ) : Prop :=
  ∃ k : ℕ, n = triangular k

@[simp]
theorem isTriangular_zero : IsTriangular 0 := ⟨0, rfl⟩

@[simp]
theorem isTriangular_one : IsTriangular 1 := ⟨1, rfl⟩

/-- The $x$-th $m$-gonal number $p_m(x) = (m - 2)x(x - 1) / 2 + x$. -/
def polygonalNumber (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

@[simp]
theorem polygonalNumber_zero (m : ℕ) : polygonalNumber m 0 = 0 := by
  simp [polygonalNumber]

@[simp]
theorem polygonalNumber_one (m : ℕ) : polygonalNumber m 1 = 1 := by
  simp [polygonalNumber]

/-- The $k$-th generalized $m$-gonal number $G_m(k) = \frac{(m - 2)k^2 - (m - 4)k}{2}$ for
$m \ge 3$ and $k \in \mathbb{Z}$ (returning $0$ if $m < 3$). -/
def generalizedPolygonalNumber (m : ℕ) (k : ℤ) : ℕ :=
  if 3 ≤ m then
    ((((m : ℤ) - 2) * k ^ 2 - ((m : ℤ) - 4) * k) / 2).toNat
  else
    0

@[simp]
theorem generalizedPolygonalNumber_zero (m : ℕ) : generalizedPolygonalNumber m 0 = 0 := by
  simp [generalizedPolygonalNumber]

end Nat
