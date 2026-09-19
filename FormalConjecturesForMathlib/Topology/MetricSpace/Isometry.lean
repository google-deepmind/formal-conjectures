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

public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-!
# The action of the isometry group

The group `α ≃ᵢ α` of isometric self-equivalences of a metric space acts on `α` by evaluation.
-/

namespace IsometryEquiv

variable {α : Type*} [PseudoEMetricSpace α]

/-- The isometry group of `α` acts on `α` by evaluation. -/
instance : MulAction (α ≃ᵢ α) α where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem smul_def (f : α ≃ᵢ α) (x : α) : f • x = f x := rfl

end IsometryEquiv
