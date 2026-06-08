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

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Distance from a vertex to a finite set. -/
noncomputable def distToSet (G : SimpleGraph α) (v : α) (S : Set α) : ℕ :=
  if h : S.toFinset.Nonempty then
    (S.toFinset.image (fun s => G.dist v s)).min' (Finset.Nonempty.image h _)
  else 0

/-- Average distance of `G`. -/
noncomputable def averageDistance (G : SimpleGraph α) : ℝ :=
  if Fintype.card α > 1 then
    (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (G.dist u v : ℝ)) /
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))
  else
    0

/-- The floor of the average distance of `G`. -/
noncomputable def path (G : SimpleGraph α) : ℕ :=
  if G.Connected then
    Nat.floor (averageDistance G)
  else
    0

/-- Auxiliary quantity `ecc` used in conjecture 34. -/
noncomputable def ecc (G : SimpleGraph α) (S : Set α) : ℕ :=
  let s_comp := Finset.univ.filter (fun v => v ∉ S)
  if h : s_comp.Nonempty then
    (s_comp.image (fun v => distToSet G v S)).max' (Finset.Nonempty.image h _)
  else 0

/-- Average distance from all vertices to a given set. -/
noncomputable def distavg (G : SimpleGraph α) (S : Set α) : ℝ :=
  if Fintype.card α > 0 then
    (∑ v ∈ Finset.univ, (distToSet G v S : ℝ)) / (Fintype.card α : ℝ)
  else
    0

/-- BFS expansion: add all neighbors of S to S. -/
def bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Finset α :=
  S ∪ S.biUnion (fun v => Finset.univ.filter (G.Adj v))

def bfs_dist_aux [DecidableEq α] [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (target : α) :
    ℕ → ℕ → Finset α → ℕ
  | 0, _, _ => 0
  | fuel + 1, depth, reached =>
    if target ∈ reached then depth
    else bfs_dist_aux G target fuel (depth + 1) (bfs_expand G reached)

/-- Computable graph distance via BFS.
Returns 0 if u = v or if v is unreachable from u. -/
def computable_dist (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℕ :=
  if u = v then 0
  else bfs_dist_aux G v (Fintype.card α) 1 (bfs_expand G {u})

/-- Computable average distance as a rational. -/
def computable_avg_dist (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  if Fintype.card α > 1 then
    (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (computable_dist G u v : ℚ)) /
      ((Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1))
  else 0


private lemma mem_iterate_bfs_expand_dist_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ (G.bfs_expand)^[n] {u}) : G.dist u w ≤ n := by
  induction n generalizing w with
  | zero => simp at hw; subst hw; simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hw
    rcases hw with hw | ⟨a, ha_mem, _, hadj⟩
    · exact Nat.le_succ_of_le (ih w hw)
    · by_cases ha : a = u
      · subst ha
        exact le_trans (dist_le (.cons hadj .nil))
          (by simp [Walk.length_cons])
      · by_cases hd : G.dist u a = 0
        · rw [dist_eq_zero_iff_eq_or_not_reachable] at hd
          rcases hd with rfl | hd
          · exact absurd rfl ha
          · have : ¬G.Reachable u w := fun hr =>
              hd (hr.elim (fun p => (p.append (.cons hadj.symm .nil)).reachable))
            rw [dist_eq_zero_of_not_reachable this]; omega
        · obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero hd
          have ha_dist := ih a ha_mem
          exact le_trans (dist_le (p.append (.cons hadj .nil)))
            (by simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hp]; omega)

private lemma reachable_of_mem_iterate_bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ (G.bfs_expand)^[n] {u}) : w = u ∨ G.Reachable u w := by
  induction n generalizing w with
  | zero => simp at hw; exact Or.inl hw
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hw
    rcases hw with hw | ⟨a, ha_mem, _, hadj⟩
    · exact ih w hw
    · right
      rcases ih a ha_mem with rfl | hr
      · exact hadj.reachable
      · exact hr.elim fun p => (p.append (.cons hadj .nil)).reachable

private lemma dist_le_mem_iterate_bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hdist : G.dist u w ≤ n) (hreach : w = u ∨ G.Reachable u w) :
    w ∈ (G.bfs_expand)^[n] {u} := by
  induction n generalizing w with
  | zero =>
    rcases hreach with rfl | hr
    · exact Finset.mem_singleton_self _
    · have h0 := Nat.le_zero.mp hdist
      rw [dist_eq_zero_iff_eq_or_not_reachable] at h0
      rcases h0 with h0 | h0
      · subst h0; exact Finset.mem_singleton_self _
      · exact absurd hr h0
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
    by_cases hle : G.dist u w ≤ n
    · left; exact ih w hle hreach
    · right
      have hdist_eq : G.dist u w = n + 1 := by omega
      obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist u w ≠ 0)
      have hlen : p.length = n + 1 := by omega
      refine ⟨p.getVert n, ?_, Finset.mem_univ _, ?_⟩
      · exact ih _ (le_trans (dist_le (p.take n))
          (by rw [Walk.take_length]; omega)) (Or.inr (p.take n).reachable)
      · have := p.adj_getVert_succ (show n < p.length from by omega)
        rwa [show n + 1 = p.length from by omega, p.getVert_length] at this

theorem dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) :
    G.dist u v = computable_dist G u v := by
  unfold computable_dist
  split_ifs with h
  · subst h; simp [dist_self]
  · symm
    suffices hsuff : ∀ (fuel depth : ℕ) (reached : Finset α),
        (∀ w, w ∈ reached ↔ w ∈ (G.bfs_expand)^[depth] {u}) →
        (∀ d, d < depth → v ∉ (G.bfs_expand)^[d] {u}) →
        fuel + depth ≥ Fintype.card α + 1 →
        G.bfs_dist_aux v fuel depth reached = G.dist u v by
      exact hsuff (Fintype.card α) 1 (G.bfs_expand {u})
        (fun w => by simp)
        (fun d hd => by
          have := Nat.lt_of_lt_of_le hd (Nat.le_refl 1)
          interval_cases d; simp [Finset.mem_singleton]; exact Ne.symm h)
        (by omega)
    intro fuel
    induction fuel with
    | zero =>
      intro depth reached h_inv h_not_found h_fuel
      simp [bfs_dist_aux]
      symm; rw [dist_eq_zero_iff_eq_or_not_reachable]
      right; intro hr
      have hpos := hr.pos_dist_of_ne h
      obtain ⟨p, hp_path, hp_len⟩ := hr.exists_path_of_dist
      have : G.dist u v < depth := by
        calc G.dist u v = p.length := hp_len.symm
          _ < Fintype.card α := hp_path.length_lt
          _ < depth := by omega
      exact h_not_found (G.dist u v) this
        (dist_le_mem_iterate_bfs_expand G u v _ (le_refl _) (Or.inr hr))
    | succ fuel ih =>
      intro depth reached h_inv h_not_found h_fuel
      simp only [bfs_dist_aux]
      split_ifs with hv
      · -- v ∈ reached = iterate^depth {u}. Show depth = dist u v.
        have hle := mem_iterate_bfs_expand_dist_le G u v depth ((h_inv v).mp hv)
        -- dist u v ≥ depth: if dist < depth, v ∈ iterate^(dist u v), contradicts h_not_found
        by_contra hne
        have hlt : G.dist u v < depth := by omega
        have hreach : G.Reachable u v := by
          rcases reachable_of_mem_iterate_bfs_expand G u v depth ((h_inv v).mp hv) with rfl | hr
          · exact absurd rfl h
          · exact hr
        exact h_not_found (G.dist u v) hlt
          (dist_le_mem_iterate_bfs_expand G u v _ (le_refl _) (Or.inr hreach))
      · -- v ∉ reached. Recurse.
        have h_inv' : ∀ w, w ∈ G.bfs_expand reached ↔
            w ∈ (G.bfs_expand)^[depth + 1] {u} := by
          intro w
          have heq : G.bfs_expand reached = G.bfs_expand ((G.bfs_expand)^[depth] {u}) := by
            ext x; simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_filter, h_inv]
          rw [heq, Function.iterate_succ', Function.comp]
        exact ih (depth + 1) (G.bfs_expand reached) h_inv'
          (fun d hd => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
            · exact h_not_found d (by omega)
            · subst hd; rwa [h_inv] at hv)
          (by omega)

theorem avg_dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    averageDistance G = (computable_avg_dist G : ℝ) := by
  unfold averageDistance computable_avg_dist
  split_ifs with h
  · -- numerator equality
    have hnum : (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (G.dist u v : ℝ)) =
        ↑(∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (computable_dist G u v : ℚ)) := by
      push_cast
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      simp [dist_eq_computable]
    rw [hnum]
    push_cast
    ring
  · simp


end SimpleGraph
