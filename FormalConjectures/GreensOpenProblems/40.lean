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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 40

*Reference:* [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)

Let $r$ be a fixed positive integer, and let $H(r)$ be the Hamming ball of radius $r$ in $\mathbb{F}_2^n$. Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and $|V_n| = (f(r) + o(1))\frac{2^n}{|H(r)|}$. Does $f(r) \to \infty$?
-/

open Filter Topology Fintype
open scoped Pointwise

namespace Green40

def hammingBall (n r : ℕ) : Set (Fin n → ZMod 2) :=
  {x | (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ r}

def isCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  (V : Set (Fin n → ZMod 2)) + hammingBall n r = Set.univ

def sequence_exists (r : ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ n in atTop, ∃ V : Submodule (ZMod 2) (Fin n → ZMod 2),
    isCoveringSubspace n r V ∧
    |(Nat.card V : ℝ) * (Nat.card (hammingBall n r) : ℝ) / (2 ^ n : ℝ) - c| < ε

noncomputable def f (r : ℕ) : ℝ := sInf {c : ℝ | sequence_exists r c}

/-- Does $f(r) \to \infty$? -/
@[category research open, AMS 5 94]
theorem green_40 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

def isCoveringFinset (n r : ℕ) (V : Finset (Fin n → ZMod 2)) : Prop :=
  (V : Set (Fin n → ZMod 2)) + hammingBall n r = Set.univ

def subset_sequence_exists (r : ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ n in atTop, ∃ V : Finset (Fin n → ZMod 2),
    isCoveringFinset n r V ∧
    |(V.card : ℝ) * (Nat.card (hammingBall n r) : ℝ) / (2 ^ n : ℝ) - c| < ε

noncomputable def f_tilde (r : ℕ) : ℝ := sInf {c : ℝ | subset_sequence_exists r c}

/-- Does $\tilde{f}(r) \to \infty$? -/
@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop atTop := by
  sorry

end Green40
