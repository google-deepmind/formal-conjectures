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

@[category test, AMS 5]
theorem isSunflowerWithKernel_empty (S : Set α) : IsSunflowerWithKernel {} S := by
  simp [IsSunflowerWithKernel]

@[category test, AMS 5]
theorem isSunflowerWithKernel_singleton (S : Set α) (A : Set α) :
    IsSunflowerWithKernel {A} S := by
  simp [IsSunflowerWithKernel]

/--
A sunflower $F$ is a collection of sets in which all possible distinct pairs of sets share the
same intersection.
-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

@[category test, AMS 5]
theorem isSunflower_empty : IsSunflower (∅ : Set (Set α)) := by
  simp [IsSunflower, isSunflowerWithKernel_empty]

@[category test, AMS 5]
theorem isSunflower_singleton (A : Set α) : IsSunflower {A} := by
  simp [IsSunflower, isSunflowerWithKernel_singleton]

/--
Let $f(n,k)$ be minimal such that every $F$ family of $n$-uniform sets with $|F| \ge f(n,k)$
contains a $k$-sunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

@[category test, AMS 5]
theorem f_0_1 : f 0 1 = 1 := by
  refine IsLeast.csInf_eq ⟨fun F hF ↦ ?_, fun n hn ↦ n.pos_of_ne_zero fun hn₀ ↦ ?_⟩
  · obtain ⟨A, hA⟩ := F.nonempty_of_ncard_ne_zero (by omega)
    exact ⟨{A}, by simpa using ⟨hA, isSunflower_singleton _⟩⟩
  · obtain ⟨S, hS⟩ := (hn (α := ℕ) {} (by simpa))
    simp_all [bot_unique hS.1]

/--
Is it true that $f(n,k) < c_k^n$ for some constant $c_k>0$ and for all $n > 0$?
-/
@[category research open, AMS 5]
theorem erdos_20 :
    (∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n ↔ answer(sorry)) := by
  sorry

-- TODO(firsching): add the various known bounds as variants.
