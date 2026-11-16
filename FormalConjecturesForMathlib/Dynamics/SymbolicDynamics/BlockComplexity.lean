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

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.Order.LiminfLimsup

/-!
# Block complexity and entropy of a sequence

The block complexity $p(n, a)$ of a sequence $a$ is the number of distinct blocks of $n$
consecutive terms of $a$. The entropy of $a$ is the exponential growth rate of $p(n, a)$.

An eventually periodic sequence has bounded block complexity and zero entropy. In particular
$p(n, a) \le n$ for some $n \ge 1$. This is the easy direction of the Morse–Hedlund theorem.

*References:*
- [AS03] Allouche, Jean-Paul, and Jeffrey Shallit. "Automatic sequences: theory, applications,
  generalizations." Cambridge University Press, 2003. Chapter 10.
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Vol. 193. Cambridge University Press, 2012. Chapter 10.

## Main definitions

* `SymbolicDynamics.blockComplexity`: the number of distinct blocks of length `n` of a sequence.
* `SymbolicDynamics.blockEntropy`: the entropy of a sequence.
* `SymbolicDynamics.IsEventuallyPeriodic`: a sequence is eventually periodic.
-/

@[expose] public section

open Filter

open scoped ENNReal

namespace SymbolicDynamics

/--
The block complexity $p(n, a)$ of a sequence $a$, that is, the number of distinct blocks
$a_k a_{k+1} \cdots a_{k+n-1}$ of $n$ consecutive terms of $a$. It is `⊤` when $n \ge 1$ and
$a$ takes infinitely many values.
-/
noncomputable def blockComplexity {α : Type*} (a : ℕ → α) (n : ℕ) : ℝ≥0∞ :=
  {w : Fin n → α | ∃ k, ∀ i, w i = a (k + i)}.encard

/--
The entropy of a sequence $a$,
$$E(a) = \lim_{n \to \infty} \frac{\log p(n, a)}{n}.$$
The limit exists because $n \mapsto \log p(n, a)$ is subadditive, so it agrees with the `limsup`
used here. The value is `⊤` exactly when $a$ takes infinitely many values.
-/
noncomputable def blockEntropy {α : Type*} (a : ℕ → α) : EReal :=
  limsup (fun n : ℕ ↦ (blockComplexity a n).log / (n : EReal)) atTop

/-- A constant sequence has exactly one block of each length. -/
theorem blockComplexity_const {α : Type*} (c : α) (n : ℕ) :
    blockComplexity (fun _ ↦ c) n = 1 := by
  have h : {w : Fin n → α | ∃ k : ℕ, ∀ i, w i = (fun _ : ℕ ↦ c) (k + (i : ℕ))}
      = {fun _ ↦ c} := by
    ext w
    simp [funext_iff]
  simp only [blockComplexity, h, Set.encard_singleton, ENat.toENNReal_one]

/-- A constant sequence has zero entropy. -/
theorem blockEntropy_const {α : Type*} (c : α) : blockEntropy (fun _ ↦ c) = 0 := by
  simp [blockEntropy, blockComplexity_const]

/-- Every sequence has at least one block of each length. -/
theorem one_le_blockComplexity {α : Type*} (a : ℕ → α) (n : ℕ) : 1 ≤ blockComplexity a n := by
  have : ({fun i : Fin n ↦ a (0 + i)} : Set _) ⊆ {w : Fin n → α | ∃ k, ∀ i, w i = a (k + i)} := by
    rintro w rfl
    exact ⟨0, fun i ↦ rfl⟩
  simpa [blockComplexity] using ENat.toENNReal_le.2 (Set.encard_le_encard this)

/-- The block complexity is monotone: every block of length $n$ extends to a block of length
$n + 1$. -/
theorem blockComplexity_mono {α : Type*} (a : ℕ → α) : Monotone (blockComplexity a) := by
  refine monotone_nat_of_le_succ fun n ↦ ENat.toENNReal_le.2 ?_
  calc _ ≤ ((fun (w : Fin (n + 1) → α) (i : Fin n) ↦ w i.castSucc) ''
        {w | ∃ k, ∀ i, w i = a (k + i)}).encard := by
        refine Set.encard_le_encard ?_
        rintro w ⟨k, hk⟩
        exact ⟨fun i ↦ a (k + i), ⟨k, fun i ↦ rfl⟩, funext fun i ↦ (hk i).symm⟩
    _ ≤ _ := Set.encard_image_le _ _

/-- A sequence $a$ is eventually periodic if there is a period $p > 0$ with $a(n + p) = a(n)$ for
all sufficiently large $n$. -/
def IsEventuallyPeriodic {α : Type*} (a : ℕ → α) : Prop :=
  ∃ p > 0, ∀ᶠ n in atTop, a (n + p) = a n

/-- An eventually periodic sequence has bounded block complexity. -/
theorem IsEventuallyPeriodic.blockComplexity_le {α : Type*} {a : ℕ → α}
    (h : IsEventuallyPeriodic a) : ∃ C : ℕ, 0 < C ∧ ∀ n, blockComplexity a n ≤ C := by
  obtain ⟨p, hp, hN⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hN
  have hper (m n : ℕ) (hn : N ≤ n) : a (n + m * p) = a n := by
    induction m with
    | zero => simp
    | succ m ih => rw [add_mul, one_mul, ← add_assoc, hN _ (by nlinarith), ih]
  refine ⟨N + p, by omega, fun n ↦ ?_⟩
  have : {w : Fin n → α | ∃ k, ∀ i, w i = a (k + i)} ⊆
      (fun k (i : Fin n) ↦ a (k + i)) '' ↑(Finset.range (N + p)) := by
    rintro w ⟨k, hk⟩
    by_cases hk' : k < N + p
    · exact ⟨k, by simpa using hk', funext fun i ↦ (hk i).symm⟩
    · have h1 := Nat.mod_add_div' (k - N) p
      have h2 := Nat.mod_lt (k - N) hp
      refine ⟨N + (k - N) % p, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)),
        funext fun i ↦ ?_⟩
      dsimp only
      rw [hk, ← hper ((k - N) / p) (N + (k - N) % p + i) (by omega)]
      congr 1
      omega
  have := (Set.encard_le_encard this).trans (Set.encard_image_le _ _)
  rw [Set.encard_coe_eq_coe_finsetCard] at this
  simpa [blockComplexity] using ENat.toENNReal_le.2 this

/-- An eventually periodic sequence satisfies $p(n, a) \le n$ for some $n \ge 1$. This is the
easy direction of the Morse–Hedlund theorem. -/
theorem IsEventuallyPeriodic.exists_blockComplexity_le {α : Type*} {a : ℕ → α}
    (h : IsEventuallyPeriodic a) : ∃ n, 0 < n ∧ blockComplexity a n ≤ n := by
  obtain ⟨C, hC, hle⟩ := h.blockComplexity_le
  exact ⟨C, hC, hle C⟩

/-- An eventually periodic sequence has zero entropy. -/
theorem IsEventuallyPeriodic.blockEntropy_eq_zero {α : Type*} {a : ℕ → α}
    (h : IsEventuallyPeriodic a) : blockEntropy a = 0 := by
  obtain ⟨C, hC, hle⟩ := h.blockComplexity_le
  have hlim : Tendsto (fun n : ℕ ↦ ((Real.log C / n : ℝ) : EReal)) atTop (nhds 0) :=
    (continuous_coe_real_ereal.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat _)
  refine le_antisymm ((limsup_le_limsup (Eventually.of_forall fun n ↦ ?_)).trans_eq
    hlim.limsup_eq) (le_limsup_of_le (by isBoundedDefault) fun x hx ↦ ?_)
  · rw [EReal.coe_div, EReal.coe_coe_eq_natCast, ← ENNReal.log_ofReal_of_pos (by positivity),
      ENNReal.ofReal_natCast]
    exact EReal.div_le_div_right_of_nonneg (by positivity) (ENNReal.log_le_log (hle n))
  · obtain ⟨n, hn⟩ := hx.exists
    refine le_trans (EReal.div_nonneg ?_ (by positivity)) hn
    simpa using ENNReal.log_le_log (one_le_blockComplexity a n)

end SymbolicDynamics
