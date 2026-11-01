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

public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-!
# Non-degenerate Hessians

Mathlib has no Hessian or Morse theory API. This file defines non-degeneracy of the second
derivative of a function at a point, as used to state that a critical point is non-degenerate.
-/

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Hessian of `f` at `x` is non-degenerate: the bilinear form
$(v, w) \mapsto D^2 f(x)[v, w]$ has trivial left kernel. -/
def HasNondegenerateHessianAt (f : E → F) (x : E) : Prop :=
  ∀ v ≠ 0, ∃ w, iteratedFDeriv 𝕜 2 f x ![v, w] ≠ 0

/-- On the zero space every Hessian is non-degenerate. -/
theorem HasNondegenerateHessianAt.of_subsingleton [Subsingleton E] (f : E → F) (x : E) :
    HasNondegenerateHessianAt 𝕜 f x :=
  fun v hv ↦ (hv (Subsingleton.elim v 0)).elim

/-- A constant function has a degenerate Hessian on a nonzero space. -/
theorem not_hasNondegenerateHessianAt_const [Nontrivial E] (c : F) (x : E) :
    ¬HasNondegenerateHessianAt 𝕜 (fun _ : E ↦ c) x := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  simpa [HasNondegenerateHessianAt, iteratedFDeriv_const_of_ne two_ne_zero] using ⟨v, hv⟩
