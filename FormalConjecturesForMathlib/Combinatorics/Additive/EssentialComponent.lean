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

public import Mathlib.Combinatorics.Schnirelmann

/-!
# Essential components
-/

@[expose] public section

open scoped Pointwise

/--
We say that $A\subset \mathbb{N}$ is an essential component if $d_s(A \oplus B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann density.
Here, the sumset is the appropriate one for Schnirelmann density, $A \oplus B = \{a+b \mid a \in A \cup \{0\}, b \in B \cup \{0\}\}$ (i.e. $(A \cup \{0\}) + (B \cup \{0\})$).
This avoids the trivial case where the sumset misses $1$ simply because neither $A$ nor $B$ contains $0$.
-/
def Set.IsEssentialComponent (A : Set ℕ) : Prop :=
  open scoped Classical in
  ∀ B : Set ℕ,
    let b := schnirelmannDensity B;
    0 < b → b < 1 → schnirelmannDensity ((A ∪ {0}) + (B ∪ {0})) > b

/-- A superset of an essential component is an essential component. -/
theorem Set.IsEssentialComponent.mono {A A' : Set ℕ}
    (hA : A.IsEssentialComponent) (h : A ⊆ A') : A'.IsEssentialComponent := by
  classical
  intro B
  dsimp only
  intro hB₀ hB₁
  refine (hA B hB₀ hB₁).trans_le (schnirelmannDensity_le_of_subset ?_)
  exact Set.add_subset_add (Set.union_subset_union_left _ h) le_rfl
