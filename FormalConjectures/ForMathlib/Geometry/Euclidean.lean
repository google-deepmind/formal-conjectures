/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Analysis.InnerProductSpace.PiL2
import FormalConjectures.ForMathlib.Data.Set.Triplewise

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open scoped EuclideanGeometry

def isIsosceles {n : ℕ} (x y z : ℝ^n) :=
  dist x y = dist y z ∨ dist y z = dist x z ∨ dist x y = dist x z

def isoscelesSet {n : ℕ} (A : Set (ℝ^n)) := A.Triplewise (isIsosceles · · ·)
