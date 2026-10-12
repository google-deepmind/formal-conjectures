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

public import FormalConjecturesUtil

/-!
# Erdős Problem 131

*References:*
- [erdosproblems.com/131](https://www.erdosproblems.com/131)
- [ELRSS99] Erdős, P. and Lev, V. and Rauzy, G. and Sándor, C. and Sárközy, A., *Greedy
  algorithm, arithmetic progressions, subset sums and divisibility*. Discrete Math. (1999),
  119-135.
- [PhZa24] Pham, H. T. and Zakharov, D., *Sharp bound for the Erdős–Straus non-averaging set
  problem*. [arXiv:2410.14624](https://arxiv.org/abs/2410.14624) (2024).
-/

@[expose] public section

open Filter Topology

namespace Erdos131

/-- A finite set $A$ of naturals is *non-dividing* if no $a \in A$ divides the sum of the
elements of any nonempty subset $S \subseteq A \setminus \{a\}$. -/
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty → ¬ a ∣ ∑ x ∈ S, x

instance (A : Finset ℕ) : Decidable (NonDividing A) := by
  unfold NonDividing; infer_instance

/-- $F(N)$ is the maximal size of a non-dividing subset of $\{1, \dots, N\}$. -/
def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonDividing).sup Finset.card

/-- $F(N)$ is attained: some non-dividing $A \subseteq \{1, \dots, N\}$ has exactly $F(N)$
elements. -/
@[category API, AMS 11]
theorem exists_card_eq_F (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, NonDividing A ∧ A.card = F N := by
  obtain ⟨A, hA, h⟩ := Finset.exists_mem_eq_sup
    (((Finset.Icc 1 N).powerset).filter NonDividing)
    ⟨∅, by simp [NonDividing]⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, h.symm⟩

/-- Every non-dividing $A \subseteq \{1, \dots, N\}$ has at most $F(N)$ elements. -/
@[category API, AMS 11]
theorem card_le_F {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hnd : NonDividing A) :
    A.card ≤ F N :=
  Finset.le_sup (f := Finset.card) (by simp [hA, hnd])

/-- Trivial upper bound: $F(N) \le N$. -/
@[category API, AMS 11]
theorem F_le (N : ℕ) : F N ≤ N := by
  obtain ⟨A, hA, -, h⟩ := exists_card_eq_F N
  simpa [← h] using Finset.card_le_card hA

/-- $F$ is monotone. -/
@[category API, AMS 11]
theorem F_mono : Monotone F := fun _ _ hMN =>
  let ⟨_, hA, hnd, h⟩ := exists_card_eq_F _
  h ▸ card_le_F (hA.trans (Finset.Icc_subset_Icc_right hMN)) hnd

/-- Trivial lower bound: for $N \ge 1$, the singleton $\{N\}$ is non-dividing, so
$1 \le F(N)$. -/
@[category API, AMS 11]
theorem one_le_F {N : ℕ} (hN : 1 ≤ N) : 1 ≤ F N := by
  have h := card_le_F (N := N) (A := {N}) (by simp [hN]) (by
    intro a ha S hS hne
    have : S = ∅ := by simpa [Finset.mem_singleton.1 ha] using hS
    simp [this] at hne)
  simpa using h

/-- Every non-dividing set is non-averaging. Pham and Zakharov [PhZa24] proved that a
non-averaging subset of $\{1, \dots, N\}$ has size at most $N^{1/4 + o(1)}$, so
$F(N) \le N^{1/4 + o(1)}$. -/
@[category research solved, AMS 11]
theorem erdos_131.variants.pham_zakharov :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, (F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + f N) := by
  sorry

/-- Erdős, Lev, Rauzy, Sándor and Sárközy [ELRSS99] proved $F(N) < 3 N^{1/2} + 1$. -/
@[category research solved, AMS 11]
theorem erdos_131.variants.elrss (N : ℕ) : (F N : ℝ) < 3 * Real.sqrt N + 1 := by
  sorry

/--
Let $F(N)$ be the maximal size of $A \subseteq \{1, \dots, N\}$ such that no $a \in A$ divides
the sum of any distinct elements of $A \setminus \{a\}$. Is it true that
$F(N) > N^{1/2 - o(1)}$?

The answer is no, by the bound of Pham and Zakharov [PhZa24]
(`erdos_131.variants.pham_zakharov`).
-/
@[category research solved, AMS 11]
theorem erdos_131 : answer(False) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 - f N) < (F N : ℝ) := by
  change False ↔ _
  refine ⟨False.elim, ?_⟩
  rintro ⟨f, hf, hlow⟩
  obtain ⟨g, hg, hup⟩ := erdos_131.variants.pham_zakharov
  have hf' : ∀ᶠ N : ℕ in atTop, f N < 1 / 8 := hf.eventually (gt_mem_nhds (by norm_num))
  have hg' : ∀ᶠ N : ℕ in atTop, g N < 1 / 8 := hg.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN1, h1, h2, h3, h4⟩ :=
    ((eventually_ge_atTop 1).and (hlow.and (hup.and (hf'.and hg')))).exists
  have hle : (N : ℝ) ^ ((1 : ℝ) / 4 + g N) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - f N) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
  linarith

end Erdos131
