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
# Mertens's conjecture for local stable matchings on a ring

*Reference:* S. Mertens, [Random Stable Matchings](https://arxiv.org/abs/cond-mat/0509221),
*J. Stat. Mech.* (2005) P10008, Section 3.2, Conjecture 3, equation (15),
[page 7](https://arxiv.org/pdf/cond-mat/0509221#page=7).

This is the periodic one-dimensional grid with neighborhood range two. Each agent independently
ranks its four neighbors uniformly and prefers every neighbor to being single. We use $n+5$
vertices so that the neighbors are distinct. Matchings may leave agents single.
-/

@[expose] public section

namespace Arxiv.«0509221»

/-- The offsets $1,2,-1,-2$ in the cyclic group with $n+5$ vertices. -/
def offset (n : ℕ) : Fin 4 → Fin (n + 5) :=
  ![⟨1, by omega⟩, ⟨2, by omega⟩, ⟨n + 4, by omega⟩, ⟨n + 3, by omega⟩]

/-- The four neighbor offsets are distinct at every permitted market size. -/
@[category API, AMS 5]
theorem offset_injective (n : ℕ) : Function.Injective (offset n) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [offset, Fin.ext_iff]

/-- No neighbor offset is zero. -/
@[category API, AMS 5]
theorem offset_ne_zero (n : ℕ) (s : Fin 4) : offset n s ≠ 0 := by
  fin_cases s <;> simp [offset, Fin.ext_iff]

/-- The neighborhood contains the reverse of every offset. -/
@[category API, AMS 5]
theorem exists_offset_neg (n : ℕ) (s : Fin 4) : ∃ t, offset n t = -(offset n s) := by
  fin_cases s
  · refine ⟨2, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def, Nat.mod_eq_of_lt (show n + 4 < n + 5 by omega)]
  · refine ⟨3, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def, Nat.mod_eq_of_lt (show n + 3 < n + 5 by omega)]
  · refine ⟨0, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def]
  · refine ⟨1, ?_⟩
    apply Fin.ext
    have h := Nat.mod_eq_of_lt (show 2 < n + 5 by omega)
    simpa [offset, Fin.neg_def] using h.symm

/-- Edges join agents at cyclic distance one or two. -/
def ring (n : ℕ) : SimpleGraph (Fin (n + 5)) where
  Adj x y := ∃ s, y = x + offset n s
  symm := ⟨by
    intro x y ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_offset_neg n s
    exact ⟨t, by simp [hs, ht]⟩⟩
  loopless := ⟨by
    intro x ⟨s, hs⟩
    apply offset_ne_zero n s
    apply add_left_cancel (a := x)
    simpa using hs.symm⟩

/-- A profile assigns each vertex a permutation of the four neighbor labels, as ranks. -/
abbrev Profile (n : ℕ) := Fin (n + 5) → Equiv.Perm (Fin 4)

/-- Neighbor ranks run from zero to three; being single has rank four.
Values on other non-neighbors are also four and are ignored by acceptability. -/
noncomputable def rank {n : ℕ} (p : Profile n) (x y : Fin (n + 5)) : ℕ :=
  if h : ∃ s, y = x + offset n s then (p x (Classical.choose h)).val else 4

/-- A listed neighbor receives its prescribed rank. -/
@[category API, AMS 5]
theorem rank_neighbor {n : ℕ} (p : Profile n) (x : Fin (n + 5)) (s : Fin 4) :
    rank p x (x + offset n s) = (p x s).val := by
  have h : ∃ t, x + offset n s = x + offset n t := ⟨s, rfl⟩
  rw [rank, dif_pos h]
  have he : Classical.choose h = s :=
    offset_injective n (add_left_cancel (Classical.choose_spec h).symm)
  rw [he]

/-- Being single has rank four. -/
@[category API, AMS 5]
theorem rank_self {n : ℕ} (p : Profile n) (x : Fin (n + 5)) : rank p x x = 4 := by
  have h : ¬ ∃ s, x = x + offset n s := (ring n).irrefl
  rw [rank, dif_neg h]

/-- Every neighbor is preferable to being single. -/
@[category API, AMS 5]
theorem rank_neighbor_lt_self {n : ℕ} (p : Profile n) (x : Fin (n + 5)) (s : Fin 4) :
    rank p x (x + offset n s) < rank p x x := by
  rw [rank_neighbor, rank_self]
  exact (p x s).isLt

/-- A profile admits an acceptable stable matching, possibly with single agents. -/
def HasStableMatching {n : ℕ} (p : Profile n) : Prop :=
  ∃ μ : Roommates.Matching (Fin (n + 5)), Roommates.IsStable (ring n) (rank p) μ

/-- Probability of admitting a stable matching under independent uniform neighbor rankings.
Uniformity on the finite profile type is the product of the uniform laws on its lists. -/
noncomputable def solutionProbability (n : ℕ) : ℝ := by
  classical
  exact (Fintype.card {p : Profile n // HasStableMatching p} : ℝ) /
    Fintype.card (Profile n)

/-- Each of the $n+5$ agents independently chooses one of $24$ strict neighbor rankings. -/
@[category test, AMS 5 60]
theorem card_profile (n : ℕ) : Fintype.card (Profile n) = 24 ^ (n + 5) := by
  simp [Profile, Fintype.card_perm, Nat.factorial]

/-- The probability is nonnegative. -/
@[category test, AMS 5 60]
theorem solutionProbability_nonneg (n : ℕ) : 0 ≤ solutionProbability n := by
  unfold solutionProbability
  positivity

/-- Counting successful profiles gives a probability at most one. -/
@[category test, AMS 5 60]
theorem solutionProbability_le_one (n : ℕ) : solutionProbability n ≤ 1 := by
  classical
  unfold solutionProbability
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Fintype.card_subtype_le (fun p : Profile n ↦ HasStableMatching p)

/--
Mertens's Conjecture 3 predicts $p_N=\Theta(q^N)$ for periodic grids. For the range-two ring,
there is one $q\in(0,1)$ and positive constants bounding $p_N/q^N$ above and below for all
sufficiently large $N$. Here $N=n+5$; the same $q$ appears in both bounds.
-/
@[category research open, AMS 5 60 82]
theorem stable_matching_probability_exponential :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        c * q ^ (n + 5) ≤ solutionProbability n ∧
          solutionProbability n ≤ C * q ^ (n + 5) := by
  sorry

end Arxiv.«0509221»
