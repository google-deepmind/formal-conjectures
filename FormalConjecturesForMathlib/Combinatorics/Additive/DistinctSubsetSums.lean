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
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.ToAdditive

/-!
# Distinct subset sums and products
-/

@[expose] public section

namespace Finset

/-- All subsets have distinct products. -/
@[to_additive HasDistinctSubsetSums /-- All subsets have distinct sums. -/]
def HasDistinctSubsetProducts {M : Type*} [CommMonoid M] (A : Finset M) : Prop :=
  Set.InjOn (fun S : Finset M ↦ ∏ n ∈ S, n) (A.powerset : Set (Finset M))

end Finset
