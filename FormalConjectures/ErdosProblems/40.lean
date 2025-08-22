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
import FormalConjectures.ErdosProblems.«28»

/-!
# Erdős Problem 40

*Reference:* [erdosproblems.com/40](https://www.erdosproblems.com/40)
-/

open Filter Set
open scoped Pointwise


/--
The predicate for a function $g\colon\mathbb{N} → \mathbb{R})$ that
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$.
-/
def Erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ (A : Set ℕ),
    ((fun (N : ℕ) => (N : ℝ).sqrt/(g N)) =O[atTop] (fun (N : ℕ) => ((A ∩ Set.Icc 1 N).ncard : ℝ))) →
    (limsup (fun (N : ℕ) =>
    letI a := PowerSeries.mk (indicator A 1)
    (a * a).coeff ℕ N) atTop = (⊤ : ℕ∞))

/--
Given a set of functions $\mathbb{N} → \mathbb{R})$, we assert that for all $g$ in that set,
if $g(N) → \infty$ then
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$.
-/
def Erdos40 (G : (ℕ → ℝ) → Prop) : Prop :=
    (∀ g, G g → (Tendsto g atTop atTop) → Erdos40For g)

/--
For what functions $g(N) → \infty$ is it true that
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$?
-/
@[category research open, AMS 11]
theorem erdos_40 : Erdos40 answer(sorry) := by
  sorry

/--
If we don't pose additional conditions on the functions, then this is a stronger form of the
Erdős-Turán conjecture, see Erdõs Problem 28,
(since establishing this for any function $g(N) → \infty$ would imply a positive solution to Erdős
Problem 28).
-/
@[category undergraduate, AMS 11]
theorem erdos_28_of_erdos_40 (h_erdos_40 : Erdos40 fun _ => True) : type_of% erdos_28 := by
  simp [Erdos40, Erdos40For] at h_erdos_40
  intro A hA
  apply h_erdos_40
  rotate_right
  · exact fun N => (N : ℝ).sqrt
  · rw [funext Real.sqrt_eq_rpow]
    exact (tendsto_rpow_atTop (one_half_pos)).comp (tendsto_natCast_atTop_atTop)
  · have ⟨n, hn⟩ := hA.exists_le
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.eventually_atTop.mpr
    use n + 1
    intro m hm
    have : 0 < m := by omega
    field_simp [norm_one, Real.norm_natCast, one_mul, Nat.one_le_cast, ge_iff_le]
    apply Nat.card_pos_iff.mpr
    constructor
    · by_contra h_empty
      have : m ∈ (A + A)ᶜ := by
        intro h
        replace ⟨a, ha, b, hb, h⟩ := h
        absurd h_empty
        by_cases ha' : 1 ≤ a
        · refine ⟨a, ha, ha', by bound⟩
        · exact ⟨b, hb, by simp only at h; omega, by bound⟩
      have := hn m this
      omega
    · exact (Set.finite_Icc _ _).inter_of_right A
