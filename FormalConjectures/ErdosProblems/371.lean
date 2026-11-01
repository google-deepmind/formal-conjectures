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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 371

*References:*
- [erdosproblems.com/371](https://www.erdosproblems.com/371)
- [OAI26a] OpenAI, *The joint Dickman law for consecutive integers*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf
-/

@[expose] public section

namespace Erdos371

set_option linter.style.formal_proof_palomar false in
/--
Let $P(n)$ denote the largest prime factor of $n$. Show that the set of $n$
with $P(n+1) > P(n)$ has density $\frac{1}{2}$.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof.
It proves `erdos_371.variants.real_density`, which implies this statement by
`erdos_371_of_real_density`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/JointDickman/PaperMain.lean#L21"]
theorem erdos_371 :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The form of `erdos_371` proved in [OAI26a]: the number of $2 \le n \le X$ with $P(n) < P(n+1)$,
divided by the real number $X$, tends to $\frac{1}{2}$ as $X \to \infty$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/JointDickman/PaperMain.lean#L21"]
theorem erdos_371.variants.real_density :
    Filter.Tendsto (fun X : ℝ => (((Finset.Icc 2 ⌊X⌋₊).filter fun n =>
      n.maxPrimeFac < (n + 1).maxPrimeFac).card : ℝ) / X) Filter.atTop (nhds (1 / 2)) := by
  sorry

/--
`erdos_371.variants.real_density` implies `erdos_371`. Restrict $X$ to natural numbers $b$.
The counts over $2 \le n \le b$ and over $n < b$ differ by at most $2$, and $2 / b \to 0$.
-/
@[category test, AMS 11]
theorem erdos_371_of_real_density (h : type_of% erdos_371.variants.real_density) :
    type_of% erdos_371 := by
  set F : ℕ → ℕ := fun b => ((Finset.range b).filter fun n =>
    n.maxPrimeFac < (n + 1).maxPrimeFac).card
  set G : ℕ → ℕ := fun b => ((Finset.Icc 2 b).filter fun n =>
    n.maxPrimeFac < (n + 1).maxPrimeFac).card with hG
  have hGlim : Filter.Tendsto (fun b : ℕ => (G b : ℝ) / b) Filter.atTop (nhds (1 / 2)) := by
    simpa [hG, Function.comp_def, Nat.floor_natCast] using h.comp tendsto_natCast_atTop_atTop
  have hFG (b : ℕ) : |(F b : ℝ) - G b| ≤ 2 := by
    have h1 : F b ≤ G b + 2 := by
      refine (Finset.card_le_card (t := (Finset.Icc 2 b).filter (fun n =>
        n.maxPrimeFac < (n + 1).maxPrimeFac) ∪ {0, 1}) fun n hn => ?_).trans
        ((Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_le_two))
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc,
        Finset.mem_insert, Finset.mem_singleton] at hn ⊢
      omega
    have h2 : G b ≤ F b + 1 := by
      refine (Finset.card_le_card (t := insert b ((Finset.range b).filter fun n =>
        n.maxPrimeFac < (n + 1).maxPrimeFac)) fun n hn => ?_).trans (Finset.card_insert_le _ _)
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_insert] at hn ⊢
      omega
    have h1' : (F b : ℝ) ≤ G b + 2 := by exact_mod_cast h1
    have h2' : (G b : ℝ) ≤ F b + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith
  have hdiff : Filter.Tendsto (fun b : ℕ => ((F b : ℝ) - G b) / b) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun b => ?_) (tendsto_const_div_atTop_nhds_zero_nat 2)
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hFG b) (Nat.cast_nonneg b)
  have hFlim : Filter.Tendsto (fun b : ℕ => (F b : ℝ) / b) Filter.atTop (nhds (1 / 2)) := by
    have := hGlim.add hdiff
    simp only [add_zero] at this
    refine this.congr fun b => ?_
    ring
  unfold Set.HasDensity
  refine hFlim.congr fun b => ?_
  have hS : { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n } ∩ Set.univ ∩ Set.Iio b =
      ↑((Finset.range b).filter fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity]
  rw [hS, Set.ncard_coe_finset, Set.univ_inter, ← Finset.coe_range, Set.ncard_coe_finset,
    Finset.card_range]

-- TODO: add the statements from the additional material
end Erdos371
