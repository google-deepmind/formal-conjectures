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
# Erdős Problem 1193

*References:*
- [erdosproblems.com/1193](https://www.erdosproblems.com/1193)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

@[expose] public section

open AdditiveCombinatorics Set

namespace Erdos1193

/-- Auxiliary: the representation function of `ℕ` itself is `n ↦ n + 1`. -/
@[category API, AMS 5 11]
lemma sumRep_univ_eq (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  simp [sumRep_def]

/-- Auxiliary: for `A = ℕ` and `g n = n + 1` the set in the question is all of `ℕ`. -/
@[category API, AMS 5 11]
lemma sumRep_eq_succ_set : {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1} = Set.univ := by
  ext n
  simp

/-- Auxiliary: the set in the question for `A = ℕ`, `g n = n + 1` has lower density `1`. -/
@[category API, AMS 5 11]
lemma lowerDensity_sumRep_univ :
    {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1}.lowerDensity = 1 := by
  rw [sumRep_eq_succ_set]
  exact (Set.HasDensity.univ (β := ℕ)).liminf_eq

/-- Auxiliary: the set in the question for `A = ℕ`, `g n = n + 1` has upper density `1`. -/
@[category API, AMS 5 11]
lemma upperDensity_sumRep_univ :
    {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1}.upperDensity = 1 := by
  rw [sumRep_eq_succ_set]
  exact (Set.HasDensity.univ (β := ℕ)).limsup_eq

/--
Let $A\subset \mathbb{N}$ and let $g(n)$ be a non-decreasing function of $n$ which is always $>0$.

Is the lower density of
$$\{ n : 1_A\ast 1_A(n)=g(n)\}$$
always $0$?

The answer is trivially no to both questions: indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$)
then $1_A\ast 1_A(n)=n+1$ for all $n$. Presumably Erdős had some additional restrictions on either
$g$ or $A$ in mind, but these are not recorded in [Er80].
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.parts.i : answer(False) ↔
    ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.lowerDensity = 0 := by
  refine iff_of_false not_false fun h => ?_
  have h1 := h Set.univ (fun n => n + 1) (fun _ _ hab => by simpa using hab) (fun n => by simp)
  have h2 : {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1}.lowerDensity = 0 := h1
  rw [lowerDensity_sumRep_univ] at h2
  exact one_ne_zero h2

/--
Let $A\subset \mathbb{N}$ and let $g(n)$ be a non-decreasing function of $n$ which is always $>0$.

Is the upper density of
$$\{ n : 1_A\ast 1_A(n)=g(n)\}$$
always $<c$ for some constant $c<1$?

The answer is trivially no to both questions: indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$)
then $1_A\ast 1_A(n)=n+1$ for all $n$. Presumably Erdős had some additional restrictions on either
$g$ or $A$ in mind, but these are not recorded in [Er80].
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.parts.ii : answer(False) ↔
    ∃ c < (1 : ℝ), ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.upperDensity < c := by
  refine iff_of_false not_false fun ⟨c, hc, h⟩ => ?_
  have h1 := h Set.univ (fun n => n + 1) (fun _ _ hab => by simpa using hab) (fun n => by simp)
  have h2 : {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1}.upperDensity < c := h1
  rw [upperDensity_sumRep_univ] at h2
  exact absurd hc (not_lt.2 h2.le)

/--
Indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$) then $1_A\ast 1_A(n)=n+1$ for all $n$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1193.lean"]
theorem erdos_1193.variants.sumRep_univ (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  sorry

/--
Erdős writes the upper density can be positive, but he believes it is bounded away from $1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.variants.upper_density_pos :
    ∃ (A : Set ℕ) (g : ℕ → ℕ), Monotone g ∧ (∀ n, 0 < g n) ∧
      0 < {n : ℕ | sumRep A n = g n}.upperDensity := by
  refine ⟨Set.univ, fun n => n + 1, fun _ _ hab => by simpa using hab, fun n => by simp, ?_⟩
  have h2 : {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1}.upperDensity = 1 :=
    upperDensity_sumRep_univ
  rw [show {n : ℕ | sumRep (Set.univ : Set ℕ) n = (fun n => n + 1) n}.upperDensity = 1 from h2]
  exact one_pos

end Erdos1193
