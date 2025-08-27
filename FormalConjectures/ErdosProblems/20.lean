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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 20

*Reference:* [erdosproblems.com/20](https://www.erdosproblems.com/20)
-/
universe u
variable {α : Type}

/--
A sunflower $F$ with kernel $S$ is a collection of sets in which all possible distinct pairs of sets
share the same intersection $S$.
-/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)


/--
A sunflower $F$ is a collection of sets in which all possible distinct pairs of sets share the
same intersection.
-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

/--
Let $f(n,k)$ be minimal such that every $F$ family of $n$-uniform sets with $|F| \ge f(n,k)$
contains a $k$-sunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
    sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}


/--
Is it true that $f(n,k) < c^n_k$ for some constant $c_k>0?
-/
@[category research open, AMS 5]
theorem erdos_20 : ∃ (c : ℕ → ℕ), ∀ n k, f n k < (c k)^n := by
  sorry


-- TODO(firsching): add the various known bounds as variants.
