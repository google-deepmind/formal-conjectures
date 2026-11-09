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
# Erdős Problem 415

*References:*
- [erdosproblems.com/415](https://www.erdosproblems.com/415)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
- [PPT13] Pollack, Paul and Pomerance, Carl and Treviño, Enrique,
  _Sets of monotonicity for Euler's totient function_. Ramanujan J. (2013), 379–398.
-/

@[expose] public section
namespace Erdos415
open Filter
open scoped Topology

abbrev StrictPattern (k : ℕ) := Equiv.Perm (Fin k)

/-- A permutation assigns ascending ranks to the positions of a strict block. -/
def StrictAt {k : ℕ} (π : StrictPattern k) (m : ℕ) : Prop :=
  ∀ i j : Fin k, π i < π j ↔
    (m + i.val + 1).totient < (m + j.val + 1).totient

instance {k : ℕ} (π : StrictPattern k) (m : ℕ) : Decidable (StrictAt π m) :=
  inferInstanceAs (Decidable (∀ i j : Fin k, π i < π j ↔
    (m + i.val + 1).totient < (m + j.val + 1).totient))

/-- Finite bounded occurrence search. The first block starts at one, when $m=0$. -/
def Appears {k : ℕ} (N : ℕ) (π : StrictPattern k) : Prop :=
  ∃ m : Fin (N + 1), m.val + k ≤ N ∧ StrictAt π m.val

instance {k : ℕ} (N : ℕ) (π : StrictPattern k) : Decidable (Appears N π) :=
  inferInstanceAs (Decidable (∃ m : Fin (N + 1), m.val + k ≤ N ∧ StrictAt π m.val))

def AllPatterns (N k : ℕ) : Prop := ∀ π : StrictPattern k, Appears N π

instance (N k : ℕ) : Decidable (AllPatterns N k) :=
  inferInstanceAs (Decidable (∀ π : StrictPattern k, Appears N π))

/-- Exact strict-permutation version of the source's extremal function. -/
def F (N : ℕ) : ℕ := Nat.findGreatest (AllPatterns N) N

/-- Consecutive strict monotonicity, without tie breaking. -/
def DecreasingAt (m k : ℕ) : Prop :=
  ∀ i j : Fin k, i < j → (m + j.val + 1).totient < (m + i.val + 1).totient

def IncreasingAt (m k : ℕ) : Prop :=
  ∀ i j : Fin k, i < j → (m + i.val + 1).totient < (m + j.val + 1).totient

instance (m k : ℕ) : Decidable (DecreasingAt m k) :=
  inferInstanceAs (Decidable (∀ i j : Fin k, i < j →
    (m + j.val + 1).totient < (m + i.val + 1).totient))

instance (m k : ℕ) : Decidable (IncreasingAt m k) :=
  inferInstanceAs (Decidable (∀ i j : Fin k, i < j →
    (m + i.val + 1).totient < (m + j.val + 1).totient))

def HasDecreasing (N k : ℕ) : Prop :=
  ∃ m : Fin (N + 1), m.val + k ≤ N ∧ DecreasingAt m.val k

def HasIncreasing (N k : ℕ) : Prop :=
  ∃ m : Fin (N + 1), m.val + k ≤ N ∧ IncreasingAt m.val k

instance (N k : ℕ) : Decidable (HasDecreasing N k) :=
  inferInstanceAs (Decidable (∃ m : Fin (N + 1), m.val + k ≤ N ∧ DecreasingAt m.val k))

instance (N k : ℕ) : Decidable (HasIncreasing N k) :=
  inferInstanceAs (Decidable (∃ m : Fin (N + 1), m.val + k ≤ N ∧ IncreasingAt m.val k))

def G (N : ℕ) : ℕ := Nat.findGreatest (HasDecreasing N) N

/-- Explicit literal interpretation of the second question.
This does not assert uniqueness among missing patterns. -/
def FirstMissingDecreasing : Prop := ∀ N : ℕ, ¬ HasDecreasing N (F N + 1)

/-- $k$-fold natural logarithm, using the total function Real.log. -/
noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

/-- Literal version with c unrestricted, including zero. -/
def ProposedScaleUnrestricted : Prop :=
  ∃ c : ℝ, Tendsto (fun N : ℕ => (F N : ℝ) / iterLog 3 (N : ℝ)) atTop (nhds c)

/-- The monotone asymptotic from [PPT13]. -/
def PPTMonotoneAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (G N : ℝ) /
    (iterLog 3 (N : ℝ) / iterLog 6 (N : ℝ))) atTop (nhds 1)

/-- Weak patterns are realizable rank maps, permitting equal ranks. Different
rank labels may encode the same order type; frequency uses only comparisons. -/
abbrev WeakPattern (k : ℕ) := Fin k → Fin k

def WeakAt {k : ℕ} (ρ : WeakPattern k) (m : ℕ) : Prop :=
  ∀ i j : Fin k, ρ i ≤ ρ j ↔
    (m + i.val + 1).totient ≤ (m + j.val + 1).totient

noncomputable def weakCount {k : ℕ} (ρ : WeakPattern k) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter (fun m => m + k ≤ N ∧ WeakAt ρ m)).card

/-- The natural weak order includes exactly the ties in $\phi(1),\ldots,\phi(k)$. -/
def NaturalAt (k m : ℕ) : Prop :=
  ∀ i j : Fin k, (i.val + 1).totient ≤ (j.val + 1).totient ↔
    (m + i.val + 1).totient ≤ (m + j.val + 1).totient

noncomputable def naturalCount (k N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter (fun m => m + k ≤ N ∧ NaturalAt k m)).card

/-- The natural weak order has a maximal natural density among all weak order patterns. -/
def NaturalMostLikely : Prop :=
  ∀ k : ℕ, 0 < k → ∃ d : ℝ,
    Tendsto (fun N : ℕ => (naturalCount k N : ℝ) / (N : ℝ)) atTop (nhds d) ∧
    ∀ ρ : WeakPattern k, ∃ e : ℝ,
      Tendsto (fun N : ℕ => (weakCount ρ N : ℝ) / (N : ℝ)) atTop (nhds e) ∧ e ≤ d
/-- Ties are real source data, not arbitrary tie breaking. -/
@[category API, AMS 11]
theorem initial_totient_tie : (1 : ℕ).totient = (2 : ℕ).totient := by decide

@[category API, AMS 11]
theorem all_zero (N : ℕ) : AllPatterns N 0 := by
  intro π
  refine ⟨⟨0, by omega⟩, by omega, ?_⟩
  intro i
  exact Fin.elim0 i

@[category API, AMS 11]
theorem F_le (N : ℕ) : F N ≤ N := Nat.findGreatest_le N

@[category API, AMS 11]
theorem F_spec (N : ℕ) : AllPatterns N (F N) :=
  Nat.findGreatest_spec (m := 0) (Nat.zero_le N) (all_zero N)

@[category API, AMS 11]
theorem le_F {N k : ℕ} (hkn : k ≤ N) (hk : AllPatterns N k) : k ≤ F N :=
  Nat.le_findGreatest hkn hk

@[category API, AMS 11]
theorem all_patterns_has_decreasing {N k : ℕ} (h : AllPatterns N k) : HasDecreasing N k := by
  obtain ⟨m, hm, hp⟩ := h (Fin.revPerm : StrictPattern k)
  refine ⟨m, hm, ?_⟩
  intro i j hij
  apply (hp j i).mp
  change j.rev < i.rev
  exact Fin.rev_lt_rev.mpr hij

@[category API, AMS 11]
theorem all_patterns_has_increasing {N k : ℕ} (h : AllPatterns N k) : HasIncreasing N k := by
  obtain ⟨m, hm, hp⟩ := h (Equiv.refl (Fin k))
  exact ⟨m, hm, fun i j hij => (hp i j).mp hij⟩

/-- Exact elementary bound used to compare the original scale with PPT13. -/
@[category API, AMS 11]
theorem F_le_G (N : ℕ) : F N ≤ G N :=
  Nat.le_findGreatest (F_le N) (all_patterns_has_decreasing (F_spec N))

@[category API, AMS 11]
theorem increasing_prefix {m k l : ℕ} (hlk : l ≤ k) (h : IncreasingAt m k) :
    IncreasingAt m l := by
  intro i j hij
  exact h ⟨i.val, lt_of_lt_of_le i.isLt hlk⟩
    ⟨j.val, lt_of_lt_of_le j.isLt hlk⟩ hij

@[category API, AMS 11]
theorem has_increasing_prefix {N k l : ℕ} (hlk : l ≤ k) (h : HasIncreasing N k) :
    HasIncreasing N l := by
  rcases h with ⟨m, hm, hi⟩
  exact ⟨m, by omega, increasing_prefix hlk hi⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
@[category test, AMS 11]
theorem all_three_826 : AllPatterns 826 3 := by
  intro π
  fin_cases π <;> first
    | exact ⟨⟨4, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩
    | exact ⟨⟨5, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩
    | exact ⟨⟨12, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩
    | exact ⟨⟨15, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩
    | exact ⟨⟨104, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩
    | exact ⟨⟨312, by decide⟩, by decide, by
        simp only [StrictAt, Nat.totient_eq_div_primeFactors_mul]; decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
@[category test, AMS 11]
theorem no_increasing_four_826 : ¬ HasIncreasing 826 4 := by
  simp only [HasIncreasing, IncreasingAt, Nat.totient_eq_div_primeFactors_mul]
  decide +kernel

set_option maxRecDepth 100000 in
@[category test, AMS 11]
theorem decreasing_four_826 : HasDecreasing 826 4 := by
  refine ⟨⟨822, by decide⟩, by decide, ?_⟩
  simp only [DecreasingAt, Nat.totient_eq_div_primeFactors_mul]
  decide +kernel

@[category test, AMS 11]
theorem F_826 : F 826 = 3 := by
  have hlo : 3 ≤ F 826 := le_F (by omega) all_three_826
  have hhi : F 826 < 4 := by
    by_contra h
    have hfour : 4 ≤ F 826 := by omega
    exact no_increasing_four_826
      (has_increasing_prefix hfour (all_patterns_has_increasing (F_spec 826)))
  omega

/-- Refutes the explicit strict finite-cutoff reading of question two. -/
@[category API, AMS 11]
theorem not_first_missing_decreasing : ¬ FirstMissingDecreasing := by
  intro h
  have hn := h 826
  rw [F_826] at hn
  exact hn decreasing_four_826


/--
For any $n$ let $F(n)$ be the largest $k$ such that any of the $k!$ possible ordering
patterns appears in some sequence of $\phi(m+1),\ldots,\phi(m+k)$ with $m+k\leq n$.
Is it true that $F(n)=(c+o(1))\log\log\log n$ for some constant $c$?

Here ordering patterns are strict, and $c>0$ excludes the degenerate zero leading term.
Pollack, Pomerance, and Treviño [PPT13] have proved that the maximum length of a decreasing
block is asymptotic to $\log\log\log n/\log\log\log\log\log\log n$.
Since $F(n)\leq G(n)$, the positive-scale question has a negative answer.
-/
@[category research solved, AMS 11]
theorem erdos_415.parts.i : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N : ℕ => (F N : ℝ) / iterLog 3 (N : ℝ)) atTop (nhds c) := by
  sorry

/--
Is the first pattern which fails to appear always
$\phi(m+1)>\phi(m+2)>\cdots>\phi(m+k)$?

For strict patterns, this asks whether the decreasing pattern of length $F(n)+1$
is absent for every cutoff $n$.
-/
@[category research solved, AMS 11]
theorem erdos_415.parts.ii : answer(False) ↔
    ∀ N : ℕ, ¬ HasDecreasing N (F N + 1) := by
  exact iff_of_false (by simp) not_first_missing_decreasing

/--
Pollack, Pomerance, and Treviño [PPT13] proved that the maximum length $G(n)$ of a
strictly decreasing block of consecutive totients up to $n$ satisfies
$G(n)\sim\log\log\log n/\log\log\log\log\log\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_415.variants.monotone_asymptotic : PPTMonotoneAsymptotic := by
  sorry

/-- With $c=0$ allowed, $F(n)=(c+o(1))\log\log\log n$ follows from [PPT13]. -/
@[category research solved, AMS 11]
theorem erdos_415.variants.unrestricted_scale : ProposedScaleUnrestricted := by
  sorry

end Erdos415

