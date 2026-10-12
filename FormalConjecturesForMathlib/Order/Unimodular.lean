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


public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic

@[expose] public section

/-!
# Unimodular sequences

A sequence is *unimodular* on `(a, ∞)` if it increases up to some point and decreases after it.
-/

/-- `f` is unimodular on `(a, ∞)` if it increases until some point `M > a` and decreases
thereafter. -/
def UnimodularOn (f : ℕ → ℝ) (a : ℕ) : Prop :=
  ∃ M > a, MonotoneOn f (Set.Ioc a M) ∧ AntitoneOn f (Set.Ici M)
