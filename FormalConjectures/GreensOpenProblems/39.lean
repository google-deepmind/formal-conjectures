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
# Green's Open Problem 39

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39)
- [BJR11] Bollobás, Béla, Svante Janson, and Oliver Riordan. "On covering by translates of a set."
  Random Structures & Algorithms 38.1‐2 (2011): 33-67.
-/

open Filter Topology
open scoped Pointwise

namespace Green39

/--
The proportion of subsets of $\mathbb{Z}/p\mathbb{Z}$ of size $k$ that can cover
$\mathbb{Z}/p\mathbb{Z}$ using at most $c$ translates.

If p = 0 or k > p, return 0 by convention.
-/
def proportionCoverable (p k c : ℕ) : ℚ :=
  if h : p = 0 then 0
  else if k > p then 0
  else
    have : NeZero p := ⟨h⟩
    let S : Finset (Finset (ZMod p)) := Finset.powersetCard k Finset.univ
    let coverable := S.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ)
    (coverable.card : ℚ) / (S.card : ℚ)

@[category test, AMS 5 60]
theorem proportionCoverable_p_p_1 : proportionCoverable 3 3 1 = 1 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_t_0 : proportionCoverable 5 2 0 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_2_1_2 : proportionCoverable 2 1 2 = 1 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_3_1_2 : proportionCoverable 3 1 2 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_a_gt_p : proportionCoverable 3 4 2 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_7_4_2 :
    proportionCoverable 7 4 2 = (3 : ℚ) / 5 := by
  native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_11_3_4 :
    proportionCoverable 11 3 4 = (1 : ℚ) / 3 := by
  native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_11_4_3 :
    proportionCoverable 11 4 3 = (1 : ℚ) / 6 := by
  native_decide

/--
If $A \subset \mathbb{Z}/p\mathbb{Z}$ is random, $|A| = \sqrt{p}$, can we almost surely cover
$\mathbb{Z}/p\mathbb{Z}$ with $100\sqrt{p}$ translates of $A$? [Gr24]
-/
@[category research open, AMS 5 60]
theorem green_39 : answer(sorry) ↔
    Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := Nat.sqrt p
        let c := 100 * k
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  sorry

/--
"I do not know how to answer this even with 100 replaced by 1.01." [Gr24]"
-/
@[category research open, AMS 5 60]
theorem green_39.variant_101 : answer(sorry) ↔
    Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := Nat.sqrt p
        let c := ⌊1.01 * (k : ℝ)⌋₊
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  sorry

/--
Similar questions are interesting with $\sqrt{p}$ replaced by $p^\theta$ for any $\theta \le 1/2$. [Gr24]
-/
@[category research open, AMS 5 60]
theorem green_39.variant_theta : answer(sorry) ↔
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1/2 →
    ∃ C > 1, Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := ⌊(p : ℝ) ^ θ⌋₊
        let c := ⌊C * (p : ℝ) ^ θ⌋₊
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  sorry

end Green39
