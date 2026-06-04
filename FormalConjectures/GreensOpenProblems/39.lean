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

NOTE: using $C p^\theta$ translates as stated makes the conjecture trivially false by the pigeonhole
principle. Indeed for a set of size $p^\theta$, we cover at most $C p^{2\theta}$ elements, which is
strictly less than $p$ for $\theta < 1/2$. We interpret the question as asking whether
$O(p^{1-\theta})$ translates suffice. This generalizes the main conjecture where
$\sqrt{p} = p^{1-1/2}$.
-/
@[category research solved, AMS 5 60]
theorem green_39.variant_theta : answer(False) ↔
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1/2 →
    ∃ C > 1, Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := ⌊(p : ℝ) ^ θ⌋₊
        let c := ⌊C * (p : ℝ) ^ θ⌋₊
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  constructor
  · exact False.elim
  · intro h_forall
    have h1 : 0 < (1/4 : ℝ) := by norm_num
    have h2 : (1/4 : ℝ) ≤ 1/2 := by norm_num
    rcases h_forall (1/4) h1 h2 with ⟨C, hC, hTendsto⟩
    have h_ev_nat := eventually_k_c_lt_p C
    haveI : Nonempty {q : ℕ // q.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
    have h_ev : ∀ᶠ (p : {q : ℕ // q.Prime}) in atTop,
        let k := ⌊(p.val : ℝ) ^ (1/4 : ℝ)⌋₊
        let c := ⌊C * (p.val : ℝ) ^ (1/4 : ℝ)⌋₊
        (proportionCoverable p.val k c : ℝ) = 0 := by
      rw [eventually_atTop] at h_ev_nat ⊢
      rcases h_ev_nat with ⟨N, hN⟩
      have h_prime := Nat.exists_infinite_primes N
      rcases h_prime with ⟨p, hp1, hp2⟩
      use ⟨p, hp2⟩
      intro p' hp'
      have : N ≤ p := by omega
      have hp2_le : p ≤ p'.val := hp'
      have h_lt := hN p'.val (le_trans this hp2_le)
      have h_prop := proportionCoverable_eq_zero h_lt
      exact_mod_cast h_prop
    have h_tendsto_0 : Tendsto
        (fun p : {q : ℕ // q.Prime} ↦
          let k := ⌊(p.val : ℝ) ^ (1/4 : ℝ)⌋₊
          let c := ⌊C * (p.val : ℝ) ^ (1/4 : ℝ)⌋₊
          (proportionCoverable p.val k c : ℝ))
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      exact h_ev.mono (fun x hx => hx.symm)
    have h_eq : (0 : ℝ) = 1 := tendsto_nhds_unique h_tendsto_0 hTendsto
    linarith

end Green39
