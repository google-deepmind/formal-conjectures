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
# Erdős Problem 55

*References:*
- [erdosproblems.com/55](https://www.erdosproblems.com/55)
- [BuEr85] Burr, S. A. and Erdős, P., *A Ramsey-type property in additive number theory*.
  Glasgow Math. J. (1985), 5–10.
- [CFP21] Conlon, D., Fox, J. and Pham, H. T., *Subset sums, completeness and colorings*.
  [arXiv:2104.14766](https://arxiv.org/abs/2104.14766) (2021).
-/

@[expose] public section

open Filter

namespace Erdos55

/--
`IsRamseyComplete A r`: for every $r$-colouring of $A$, every sufficiently large $n$ is the sum
of a finite set of distinct elements of $A$ that all have the same colour.

The colouring `f` is defined on all of `ℕ`; only its restriction to `A` matters. The colour of
the sum may depend on `n`.
-/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ f : ℕ → Fin r, ∃ N₀, ∀ n ≥ N₀, ∃ S : Finset ℕ,
    ↑S ⊆ A ∧ (∃ c, ∀ a ∈ S, f a = c) ∧ ∑ a ∈ S, a = n

/-- There are no `0`-colourings, so every set is vacuously Ramsey `0`-complete. -/
@[category test, AMS 5 11]
theorem isRamseyComplete_zero (A : Set ℕ) : IsRamseyComplete A 0 :=
  fun f => (f 0).elim0

/-- The empty set is not Ramsey `r`-complete for `r ≥ 1`. -/
@[category test, AMS 5 11]
theorem not_isRamseyComplete_empty {r : ℕ} (hr : 1 ≤ r) : ¬ IsRamseyComplete ∅ r := by
  intro h
  obtain ⟨N₀, hN₀⟩ := h fun _ => ⟨0, hr⟩
  obtain ⟨S, hS, -, hsum⟩ := hN₀ (N₀ + 1) (by omega)
  rw [Set.subset_empty_iff, Finset.coe_eq_empty] at hS
  simp [hS] at hsum

/-- If `A` is Ramsey `r`-complete with `r ≥ 1`, then every large `n ≤ N` is a subset sum of
`A ∩ [1, N]`. Hence `N + 1 - N₀ ≤ 2 ^ |A ∩ [1, N]|`. -/
@[category API, AMS 5 11]
theorem IsRamseyComplete.exists_le_two_pow {A : Set ℕ} {r : ℕ} (hr : 1 ≤ r)
    (hA : IsRamseyComplete A r) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N + 1 - N₀ ≤ 2 ^ (A ∩ Set.Icc 1 N).ncard := by
  classical
  obtain ⟨N₀, hN₀⟩ := hA fun _ => ⟨0, hr⟩
  choose S hSA _ hSsum using hN₀
  refine ⟨max N₀ 1, fun N => ?_⟩
  set B := (Finset.Icc 1 N).filter (· ∈ A) with hB
  have hBA : A ∩ Set.Icc 1 N = ↑B := by
    ext x
    simp [hB]
    tauto
  let T : ℕ → Finset ℕ := fun n => if h : n ≥ N₀ then (S n h).filter (1 ≤ ·) else ∅
  have hTsum : ∀ n ≥ N₀, ∑ a ∈ T n, a = n := by
    intro n hn
    simp only [T, dif_pos hn]
    rw [Finset.sum_filter_of_ne (fun x _ hx => by omega), hSsum]
  have hmaps : Set.MapsTo T (Finset.Icc (max N₀ 1) N : Set ℕ) (B.powerset : Set (Finset ℕ)) := by
    intro n hn
    simp only [Finset.coe_Icc, Set.mem_Icc, max_le_iff] at hn
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    intro a ha
    have hn0 : n ≥ N₀ := hn.1.1
    have ha' := ha
    simp only [T, dif_pos hn0, Finset.mem_filter] at ha'
    have hle : a ≤ n := by
      rw [← hTsum n hn0]
      exact Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) ha
    simp only [hB, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ha'.2, by omega⟩, hSA n hn0 ha'.1⟩
  have hinj : Set.InjOn T (Finset.Icc (max N₀ 1) N : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc, max_le_iff] at hx hy
    rw [← hTsum x hx.1.1, ← hTsum y hy.1.1, hxy]
  have := Finset.card_le_card_of_injOn T hmaps hinj
  rw [hBA, Set.ncard_coe_finset]
  simpa [Finset.card_powerset] using this

/-- A trivial lower bound: if $A$ is Ramsey $r$-complete with $r \geq 1$, then
$|A \cap \{1, \dots, N\}| \geq \log_2 N - 1$ for all large $N$. -/
@[category textbook, AMS 5 11]
theorem IsRamseyComplete.logb_sub_one_le {A : Set ℕ} {r : ℕ} (hr : 1 ≤ r)
    (hA : IsRamseyComplete A r) :
    ∀ᶠ N : ℕ in atTop, Real.logb 2 N - 1 ≤ (A ∩ Set.Icc 1 N).ncard := by
  obtain ⟨N₀, hN₀⟩ := hA.exists_le_two_pow hr
  filter_upwards [eventually_ge_atTop (2 * N₀ + 1)] with N hN
  have h1 := hN₀ N
  set k := (A ∩ Set.Icc 1 N).ncard
  have h3 : N ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [sub_le_iff_le_add, Real.logb_le_iff_le_rpow (by norm_num) hNpos,
    show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  exact_mod_cast h3

/--
A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is $r$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$. Prove any non-trivial
bounds about the growth rate of such an $A$ for $r>2$.

Conlon, Fox and Pham [CFP21] solved this for all $r \geq 2$. For every $r \geq 2$ there is a
Ramsey $r$-complete $A$ with $\lvert A\cap \{1,\ldots,N\}\rvert \ll r(\log N)^2$ for all large
$N$. This is optimal: there is some $c>0$ such that if
$\lvert A\cap \{1,\ldots,N\}\rvert \leq cr(\log N)^2$ for all large $N$, then $A$ is not
Ramsey $r$-complete. Both constants are absolute.
-/
@[category research solved, AMS 5 11]
theorem erdos_55 :
    (∃ C > (0 : ℝ), ∀ r ≥ (2 : ℕ), ∃ A : Set ℕ, IsRamseyComplete A r ∧
      ∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * r * Real.log N ^ 2) ∧
    (∃ c > (0 : ℝ), ∀ r ≥ (2 : ℕ), ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ c * r * Real.log N ^ 2) →
        ¬ IsRamseyComplete A r) := by
  sorry

/--
Burr and Erdős [BuEr85] showed for $r=2$ that there exists some $c>0$ such that it cannot be
true that $\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2$ for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.burr_erdos_lower :
    ∃ c > (0 : ℝ), ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ c * Real.log N ^ 2) →
        ¬ IsRamseyComplete A 2 := by
  sorry

/--
Burr and Erdős [BuEr85] constructed a Ramsey $2$-complete $A$ such that
$\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^3$ for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.burr_erdos_upper :
    ∃ A : Set ℕ, IsRamseyComplete A 2 ∧ ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * Real.log N ^ 3 := by
  sorry

/--
Burr has shown that the set of $k$th powers is Ramsey $r$-complete for every $r,k\geq 1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.burr_powers (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsRamseyComplete {m | ∃ n ≥ 1, m = n ^ k} r := by
  sorry

end Erdos55
