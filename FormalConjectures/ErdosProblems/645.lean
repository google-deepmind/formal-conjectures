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
# Erdős Problem 645

*References:*
- [erdosproblems.com/645](https://www.erdosproblems.com/645)
- [BrLa99] Brown, Tom C. and Landman, Bruce M., Monochromatic arithmetic progressions with large
  differences. Bull. Austral. Math. Soc. (1999), 21--35.
-/


namespace Erdos645

private def hasMono (c : ℕ → Bool) : Prop :=
  ∃ x d : ℕ, x > 0 ∧ d > x ∧ c x = c (x + d) ∧ c (x + d) = c (x + 2 * d)

private lemma case_1_step (c : ℕ → Bool) (h : ¬ hasMono c) (h1 : c 1 = true)
    (h3 : c 3 = false) (n : ℕ) (hn : n ≥ 6) (hcn : c n = true) : c (n + 1) = true := by
  have e1 : 1 + (n - 1) = n := by omega
  have e2 : 1 + 2 * (n - 1) = 2 * n - 1 := by omega
  have e3 : 3 + (n - 2) = n + 1 := by omega
  have e4 : 3 + 2 * (n - 2) = 2 * n - 1 := by omega
  have h2n1 : c (2 * n - 1) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    exact h ⟨1, n - 1, by omega, by omega,
      by rw [e1, h1, hcn], by rw [e1, e2, hcn, hc]⟩
  by_contra hc; rw [Bool.not_eq_true] at hc
  exact h ⟨3, n - 2, by omega, by omega,
    by rw [e3, h3, hc], by rw [e3, e4, hc, h2n1]⟩

private lemma case_1_inductive (c : ℕ → Bool) (h : ¬ hasMono c) (h1 : c 1 = true)
    (h3 : c 3 = false) (n : ℕ) (hn : n ≥ 6) (hcn : c n = true) :
    ∀ m ≥ n, c m = true := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  induction k with
  | zero => simpa
  | succ k ih => exact case_1_step c h h1 h3 (n + k) (by omega) (ih (by omega))

private lemma eventually_constant_implies_mono (c : ℕ → Bool) (v : Bool) (N : ℕ)
    (h : ∀ n ≥ N, c n = v) : hasMono c :=
  ⟨N + 1, 2 * N + 3, by omega, by omega,
    by rw [h (N + 1) (by omega), h (N + 1 + (2 * N + 3)) (by omega)],
    by rw [h (N + 1 + (2 * N + 3)) (by omega), h (N + 1 + 2 * (2 * N + 3)) (by omega)]⟩

private lemma case_1_impossible (c : ℕ → Bool) (h1 : c 1 = true) (h3 : c 3 = false) :
    hasMono c := by
  by_contra h_no
  have hf : ∀ n ≥ 6, c n = false := by
    intro n hn; by_contra hc
    exact h_no (eventually_constant_implies_mono c true n
      (case_1_inductive c h_no h1 h3 n hn (by rw [Bool.not_eq_false] at hc; exact hc)))
  exact h_no (eventually_constant_implies_mono c false 6 hf)

private lemma case_2_step (c : ℕ → Bool) (h : ¬ hasMono c) (h1 : c 1 = true)
    (h5 : c 5 = false) (n : ℕ) (hn : n ≥ 9) (hcn : c n = true) : c (n + 2) = true := by
  have e1 : 1 + (n - 1) = n := by omega
  have e2 : 1 + 2 * (n - 1) = 2 * n - 1 := by omega
  have e3 : 5 + (n - 3) = n + 2 := by omega
  have e4 : 5 + 2 * (n - 3) = 2 * n - 1 := by omega
  have h2n1 : c (2 * n - 1) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    exact h ⟨1, n - 1, by omega, by omega,
      by rw [e1, h1, hcn], by rw [e1, e2, hcn, hc]⟩
  by_contra hc; rw [Bool.not_eq_true] at hc
  exact h ⟨5, n - 3, by omega, by omega,
    by rw [e3, h5, hc], by rw [e3, e4, hc, h2n1]⟩

private lemma case_2_inductive (c : ℕ → Bool) (h : ¬ hasMono c) (h1 : c 1 = true)
    (h5 : c 5 = false) (n : ℕ) (hn : n ≥ 9) (hcn : c n = true) :
    ∀ k, c (n + 2 * k) = true := by
  intro k; induction k with
  | zero => simpa
  | succ k ih =>
    rw [show n + 2 * (k + 1) = (n + 2 * k) + 2 from by ring]
    exact case_2_step c h h1 h5 (n + 2 * k) (by omega) ih

private lemma case_2_impossible (c : ℕ → Bool) (h1 : c 1 = true) (h5 : c 5 = false) :
    hasMono c := by
  by_contra h_no
  by_cases hex : ∃ n, n ≥ 9 ∧ c n = true
  · obtain ⟨n, hn, hcn⟩ := hex
    have hind := case_2_inductive c h_no h1 h5 n hn hcn
    exact h_no ⟨n, 2 * n, by omega, by omega,
      by rw [hcn, hind n], by rw [hind n, hind (2 * n)]⟩
  · push_neg at hex
    exact h_no (eventually_constant_implies_mono c false 9
      (fun m hm => by cases hv : c m <;> simp_all [hex m hm]))

private theorem exists_mono (c : ℕ → Bool) : hasMono c := by
  by_cases h1 : c 1 = true
  · by_cases h3 : c 3 = true
    · by_cases h5 : c 5 = true
      · exact ⟨1, 2, by omega, by omega, by rw [h1, h3], by rw [h3, h5]⟩
      · exact case_2_impossible c h1 (by rw [Bool.not_eq_true] at h5; exact h5)
    · exact case_1_impossible c h1 (by rw [Bool.not_eq_true] at h3; exact h3)
  · set c' : ℕ → Bool := fun n => !c n with hc'_def
    have hc1' : c' 1 = true := by simp [hc'_def]; rw [Bool.not_eq_true] at h1; rw [h1]
    suffices hasMono c' by
      obtain ⟨x, d, hx, hd, he1, he2⟩ := this
      refine ⟨x, d, hx, hd, ?_, ?_⟩
      · simp [hc'_def] at he1; exact he1
      · simp [hc'_def] at he2; exact he2
    by_cases h3' : c' 3 = true
    · by_cases h5' : c' 5 = true
      · exact ⟨1, 2, by omega, by omega, by rw [hc1', h3'], by rw [h3', h5']⟩
      · exact case_2_impossible c' hc1' (by rw [Bool.not_eq_true] at h5'; exact h5')
    · exact case_1_impossible c' hc1' (by rw [Bool.not_eq_true] at h3'; exact h3')

/--
If ℕ is $2$-coloured then there must exist a monochromatic three-term arithmetic progression
$x,x+d,x+2d$ such that $d>x$.

This was first proved by Brown and Landman [BrLa99], who in fact show that this is always possible
with $d>f(x)$ for any increasing function $f$.

This was formalized in Lean by Alexeev using Aristotle and ChatGPT.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos645.lean"]
theorem erdos_645 (c : ℕ → Bool) : ∃ x d, 0 < x ∧ x < d ∧
    (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) := by
  obtain ⟨x, d, hx, hd, h1, h2⟩ := exists_mono c
  exact ⟨x, d, hx, hd, c x, rfl, h1.symm, (h2 ▸ h1).symm⟩

end Erdos645
