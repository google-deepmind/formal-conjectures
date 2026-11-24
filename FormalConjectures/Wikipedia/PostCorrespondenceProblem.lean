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
# Post correspondence problem for a fixed number of word pairs

Given two lists $(u_0, \dots, u_{n-1})$ and $(v_0, \dots, v_{n-1})$ of finite words over an
alphabet of cardinality $\ge 2$, the **Post correspondence problem** asks if some nonempty index
sequence $(i_1, \dots, i_m)$ satisfies $u_{i_1} \cdots u_{i_m} = v_{i_1} \cdots v_{i_m}$.
Any finite alphabet of size $\ge 2$ embeds into `{false, true}^*` via an injective monoid
morphism without changing the pair count $n$, so formalising over `List Bool` is equivalent to the
general multi-letter formulation.

Emil Post (1946) proved that the unrestricted problem is undecidable. Fixing the number $n$ of
word pairs, Ehrenfeucht, Karhumäki, and Rozenberg (1982) proved decidability for $n \le 2$, while
Turlough Neary (2015) proved undecidability for every $n \ge 5$. Decidability for $n = 3$ and for
$n = 4$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Post_correspondence_problem)
- E. L. Post, *A variant of a recursively unsolvable problem*, Bull. Amer. Math. Soc. **52**
  (1946), 264–268.
- A. Ehrenfeucht, J. Karhumäki, and G. Rozenberg, *The (generalized) Post correspondence problem
  with lists consisting of two words is decidable*, Theoret. Comput. Sci. **21** (1982), 119–144.
- T. Neary, *Undecidability in binary tag systems and the Post correspondence problem for five
  pairs of words*, in *STACS 2015*, LIPIcs **30** (2015), 649–661.
-/

@[expose] public section

namespace PostCorrespondenceProblem

/-- A binary word-pair list `pairs` admits a correspondence match if some nonempty sequence of
valid tile indices produces equal top and bottom concatenations. -/
def HasPCPSolution (pairs : List (List Bool × List Bool)) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < pairs.length) ∧
    (idx.flatMap fun i => (pairs.getD i ([], [])).1) =
      (idx.flatMap fun i => (pairs.getD i ([], [])).2)

/-- Instance predicate for the Post correspondence problem restricted to lists of `n` word
pairs. -/
def HasFixedSizePCPSolution (n : ℕ) (pairs : List (List Bool × List Bool)) : Prop :=
  pairs.length = n ∧ HasPCPSolution pairs

/-- The empty tile list ($n = 0$) admits no nonempty valid index sequence. -/
@[category test, AMS 3 68]
theorem not_hasPCPSolution_nil : ¬ HasPCPSolution [] := by
  rintro ⟨idx, hne, hlt, -⟩
  cases idx with
  | nil => exact hne rfl
  | cons i _ => exact Nat.not_lt_zero i (hlt i List.mem_cons_self)

/-- The $2$-pair instance `[([true], [true, false]), ([false, true], [true])]` is solved by the
index sequence `[0, 1]`. -/
@[category test, AMS 3 68]
theorem hasFixedSizePCPSolution_two_example :
    HasFixedSizePCPSolution 2 [([true], [true, false]), ([false, true], [true])] :=
  ⟨rfl, [0, 1], by simp, by decide, by decide⟩

/-- The $1$-pair instance `[([true], [false])]` has no solution because the initial bits of the
two concatenations disagree. -/
@[category test, AMS 3 68]
theorem not_hasFixedSizePCPSolution_one_mismatch :
    ¬ HasFixedSizePCPSolution 1 [([true], [false])] := by
  rintro ⟨_, idx, hne, hlt, heq⟩
  cases idx with
  | nil => exact hne rfl
  | cons i _ =>
    have hi : i = 0 := Nat.lt_one_iff.mp (hlt i List.mem_cons_self)
    subst hi
    simp at heq

/-- For a $1$-element tile list `[p]`, a match exists if and only if `p.1 = p.2`. -/
@[category API, AMS 3 68]
theorem hasPCPSolution_singleton_iff (p : List Bool × List Bool) :
    HasPCPSolution [p] ↔ p.1 = p.2 := by
  refine ⟨?_, fun h => ⟨[0], by simp, by simp, by simp [h]⟩⟩
  rintro ⟨idx, hne, hlt, heq⟩
  have hzero : ∀ i ∈ idx, i = 0 := fun i hi => Nat.lt_one_iff.mp (hlt i hi)
  have hflat_len : ∀ (f : List Bool × List Bool → List Bool) (l : List ℕ),
      (∀ i ∈ l, i = 0) →
      (l.flatMap fun i => f ([p].getD i ([], []))).length = l.length * (f p).length := by
    intro f l hl
    induction l with
    | nil => simp
    | cons i rest ih =>
      have hi : i = 0 := hl i List.mem_cons_self
      have hrest : ∀ j ∈ rest, j = 0 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
      rw [List.flatMap_cons, hi, List.getD_cons_zero, List.length_append, List.length_cons,
        ih hrest]
      ring
  have hlen₁ := hflat_len Prod.fst idx hzero
  have hlen₂ := hflat_len Prod.snd idx hzero
  have hlen_pos : 0 < idx.length := List.length_pos_of_ne_nil hne
  have hlen_eq : p.1.length = p.2.length := by
    have hmul : idx.length * p.1.length = idx.length * p.2.length := by
      rw [← hlen₁, heq, hlen₂]
    exact Nat.eq_of_mul_eq_mul_left hlen_pos hmul
  cases idx with
  | nil => exact (hne rfl).elim
  | cons i rest =>
    have hi : i = 0 := hzero i List.mem_cons_self
    subst hi
    simp only [List.flatMap_cons, List.getD_cons_zero] at heq
    exact (List.append_inj heq hlen_eq).1

/-- The $1$-pair Post correspondence problem is algorithmically decidable. -/
@[category textbook, AMS 3 68]
theorem pcp_one_decidable : ComputablePred (HasFixedSizePCPSolution 1) := by
  have hp0 : Primrec fun pairs : List (List Bool × List Bool) => pairs.getD 0 ([], []) :=
    (Primrec.list_getD ([], [])).comp Primrec.id (Primrec.const 0)
  have hprim : PrimrecPred fun pairs : List (List Bool × List Bool) =>
      pairs.length = 1 ∧ (pairs.getD 0 ([], [])).1 = (pairs.getD 0 ([], [])).2 :=
    (Primrec.eq.comp Primrec.list_length (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.fst.comp hp0) (Primrec.snd.comp hp0))
  refine hprim.computablePred.of_eq fun pairs => ?_
  constructor
  · rintro ⟨hlen, heq⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨rfl, (hasPCPSolution_singleton_iff p).mpr heq⟩
  · rintro ⟨hlen, hsol⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨rfl, (hasPCPSolution_singleton_iff p).mp hsol⟩

/-- **Post's theorem (1946).** The general Post correspondence problem is undecidable. -/
@[category research solved, AMS 3 68]
theorem pcp_undecidable : ¬ ComputablePred HasPCPSolution := by
  sorry

/-- **Ehrenfeucht–Karhumäki–Rozenberg theorem (1982).** The Post correspondence problem for $2$
pairs of words is decidable. -/
@[category research solved, AMS 3 68]
theorem pcp_two_decidable : ComputablePred (HasFixedSizePCPSolution 2) := by
  sorry

/-- **Neary's theorem (2015).** For every $n \ge 5$, the Post correspondence problem for $n$ pairs
of words is undecidable. -/
@[category research solved, AMS 3 68]
theorem pcp_ge_five_undecidable (n : ℕ) (hn : 5 ≤ n) :
    ¬ ComputablePred (HasFixedSizePCPSolution n) := by
  sorry

/-- Is the Post correspondence problem for $3$ pairs of words decidable? -/
@[category research open, question, AMS 3 68]
theorem pcp_three_decidable : ComputablePred (HasFixedSizePCPSolution 3) := by
  sorry

/-- Is the Post correspondence problem for $4$ pairs of words decidable? -/
@[category research open, question, AMS 3 68]
theorem pcp_four_decidable : ComputablePred (HasFixedSizePCPSolution 4) := by
  sorry

end PostCorrespondenceProblem
