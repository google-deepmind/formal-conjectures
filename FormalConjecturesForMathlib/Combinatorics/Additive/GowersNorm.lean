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

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open scoped BigOperators
open Complex

/-!
# Gowers Norms and Multiplicative Derivatives

This file provides common definitions for the multiplicative derivative and Gowers norms
over finite groups, which are frequently used in additive combinatorics.
-/

/--
The multiplicative derivative $\Delta_h f(x) = f(x) \overline{f(x+h)}$.
-/
noncomputable def multiplicativeDerivative {G : Type*} [AddGroup G] (h : G) (f : G → ℂ) : G → ℂ :=
  fun x ↦ f x * star (f (x + h))
