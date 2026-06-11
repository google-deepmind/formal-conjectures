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
# Erdős Problem 944

*Reference:* [erdosproblems.com/944](https://www.erdosproblems.com/944)
-/

universe u
variable {V : Type u}

namespace Erdos944

open Erdos944

/--
The predicate that graph $G$ with chromatic number $k$ is such that every vertex is critical, yet
every critical set of edges has size $>r$
-/
def SimpleGraph.IsErdos944 (G : SimpleGraph V) (k r : ℕ) : Prop :=  G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)

/--
Let $k \ge 4$ and $r\ge 1$. Must there exist a graph $G$ with chromatic number $k$
 such that every vertex is critical, yet every critical set of edges has size $>r$?
-/
@[category research open, AMS 11]
theorem erdos_944 :
    answer(sorry) ↔ ∀ k ≥ 4, ∀ r ≥ 1, ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k r := by
  sorry

/--
Let $k \ge 4$. Must there exist a graph $G$ with chromatic number $k$
such that every vertex is critical, yet every critical set of edges has size $>1$?

This was conjectured by Dirac in 1970.
-/
@[category research open, AMS 11]
theorem erdos_944.variants.dirac_conjecture :
    answer(sorry) ↔ ∀ k ≥ 4, ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry


/--
Dirac's conjecture was proved, for $k=5$: There exists a graph $G$ with chromatic number $5$, such
that every vertex is critical, yet every critical set of edges has size $>1$, or in other words:
has no critical edge.

[Br92] Brown, Jason I., A vertex critical graph without critical edges. Discrete Math. (1992), 99--101
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_eq_5 :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 5 1 := by
  sorry

/--
Lattanzio [La02] proved there exist $k$-critical graphs without critical edges for all $k$ such that
$k - 1$ is not prime.

[La02] Lattanzio, John J., A note on a conjecture of {D}irac. Discrete Math. (2002), 323--330
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_sub_one_not_prime (k : ℕ) (hk : 4 ≤ k)
    (h : ¬ (k - 1).Prime) : ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
Jensen [Je02] gave an construction for $k$-critical graphs without any critical edges for all $k ≥ 5$.

[Je02] Jensen, Tommy R., Dense critical and vertex-critical graphs. Discrete Math. (2002), 63--84.
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_ge_five (k : ℕ) (hk : 5 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
The case $k=4$ and $r=1$ remains open: Are there $4$-critical graphs without any critical edges?
-/
@[category research open, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_eq_four :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1 := by
  sorry

/--
Martinsson and Steiner [MaSt25] proved for every $r \ge 1$ if $k$ is sufficiently large, depending
on $r$, there exist a graph $G$ with chromatic number $k$ such that every vertex is critical,
yet every critical set of edges has size $>r$.

[MaSt25] Martinsson, Anders and Steiner, Raphael, Vertex-critical graphs far from edge-criticality. Combin. Probab. Comput. (2025), 151--157
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.large_k_for_any_r (r : ℕ) (hr : 1 ≤ r) : ∀ᶠ k in Filter.atTop,
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k r := by
  sorry


/-
## Verified partial results for the $k=4$, $r=1$ case (6-regular subproblem)

Skottová and Steiner [SkSt25] proved that every $(4,1)$-graph (a $4$-vertex-critical
graph with no critical edge) has minimum degree and edge-connectivity at least $6$, and
asked (their Problem 5.2) whether a $6$-regular $(4,1)$-graph exists. The following are
machine-checked cores of verified computational results on that subproblem
(2026): there is no $6$-regular $4$-vertex-critical graph on $n \le 12$ or $n = 14$
vertices (and the unique one on $n = 13$ has critical edges), and in any $6$-regular
$(4,1)$-graph every $6$-edge-cut is either a vertex star or has both shores of size at
least $14$.

* `singleton_edge_critical`: the recolouring core of the singleton lemma — if a
  $3$-colouring of $G - v$ gives colour $c$ to exactly one neighbour $u$ of $v$, the
  extension by $v \mapsto c$ is proper on every edge except $uv$ (hence $uv$ is
  critical in a $4$-vertex-critical graph). Axiom-free.
* `cut_matrix_classification` (with the enumeration-completeness lemma `mem_comps`):
  exactly $21$ of the $3 	imes 3$ nonnegative matrices with entry sum $6$ have all six
  permutation-diagonal sums at least $2$ — the exact equality case of the
  Skottová–Steiner cut bound. `matrix_mem_classification` is the bridge from the
  genuine matrix form.
* `turan_count_shore`: the numeric core excluding $6$-cut shores of size $2,\dots,7$.

[SkSt25] Skottová, Ema and Steiner, Raphael, Critical edge sets in vertex-critical
graphs. arXiv:2508.08703 (2025)
-/

/-- If `φ` properly colours all edges not incident to `v` and exactly one neighbour `u` of `v` has
colour `c`, then the extension of `φ` to `v` by `c` is proper on every edge except `uv`. -/
@[category API, AMS 5]
theorem singleton_edge_critical {V : Type*} [DecidableEq V]
    (adj : V → V → Prop) (hsym : ∀ {a b}, adj a b → adj b a) (hirr : ∀ a, ¬ adj a a)
    (v u : V) (φ : V → Fin 3) (c : Fin 3)
    (huniq : ∀ w, adj v w → φ w = c → w = u)
    (hproper : ∀ a b, adj a b → a ≠ v → b ≠ v → φ a ≠ φ b) :
    ∀ a b, adj a b → ¬(a = v ∧ b = u) → ¬(a = u ∧ b = v) →
      Function.update φ v c a ≠ Function.update φ v c b := by
  intro a b hab hnab hnba
  by_cases hav : a = v
  · by_cases hbv : b = v
    · exact absurd hab (by rw [hav, hbv]; exact hirr v)
    · have hb : adj v b := by rw [← hav]; exact hab
      have hbc : φ b ≠ c := fun h => hnab ⟨hav, huniq b hb h⟩
      rw [hav, Function.update_self, Function.update_of_ne hbv]
      exact fun h => hbc h.symm
  · by_cases hbv : b = v
    · have ha : adj v a := hsym (by rw [← hbv]; exact hab)
      have hac : φ a ≠ c := fun h => hnba ⟨huniq a ha h, hbv⟩
      rw [hbv, Function.update_of_ne hav, Function.update_self]
      exact hac
    · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
      exact hproper a b hab hav hbv

/-- All length-`k` lists of naturals with sum `n` (weak compositions of `n` into `k` parts). -/
def comps : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | k + 1, n => (List.range (n + 1)).flatMap fun a => (comps k (n - a)).map (a :: ·)

/-- Completeness of the enumeration: `comps k n` contains exactly the length-`k` sum-`n` lists. -/
@[category API, AMS 5]
theorem mem_comps : ∀ k n l, l ∈ comps k n ↔ l.length = k ∧ l.sum = n := by
  intro k
  induction k with
  | zero =>
    intro n l
    match n with
    | 0 =>
      simp only [comps, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨hl, -⟩; exact List.length_eq_zero_iff.mp hl
    | m + 1 =>
      simp only [comps, List.not_mem_nil, false_iff, not_and]
      intro hl
      rw [List.length_eq_zero_iff.mp hl]
      simp
  | succ k ih =>
    intro n l
    simp only [comps, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ha, l', hl', rfl⟩
      obtain ⟨hlen, hsum⟩ := (ih (n - a) l').mp hl'
      refine ⟨by simp [hlen], ?_⟩
      simp only [List.sum_cons, hsum]
      omega
    · rintro ⟨hlen, hsum⟩
      match l with
      | [] => simp at hlen
      | a :: l' =>
        simp only [List.sum_cons] at hsum
        simp only [List.length_cons, Nat.add_left_inj] at hlen
        exact ⟨a, by omega, l', (ih (n - a) l').mpr ⟨hlen, by omega⟩, rfl⟩

/-- All six permutation-diagonal sums of the 3×3 matrix `[a,b,c; d,e,f; g,h,i]` are ≥ 2. -/
def diagOK : List ℕ → Bool
  | [a, b, c, d, e, f, g, h, i] =>
    decide (2 ≤ a + e + i) && decide (2 ≤ a + f + h) && decide (2 ≤ b + d + i) &&
    decide (2 ≤ b + f + g) && decide (2 ≤ c + d + h) && decide (2 ≤ c + e + g)
  | _ => false

set_option maxRecDepth 100000 in
/-- Exactly 21 of the 3003 sum-6 3×3 ℕ-matrices have all six permutation-diagonal sums ≥ 2:
the exact equality case of the Skottová–Steiner 6-edge-cut bound for `(4,1)`-graphs. -/
@[category API, AMS 5]
theorem cut_matrix_classification : ((comps 9 6).filter diagOK).length = 21 := by decide

/-- Matrix form of the classification membership: any 3×3 ℕ-matrix with total sum 6 whose
permutation diagonals all have sum ≥ 2 appears (row-major) in the 21-element enumeration of
`cut_matrix_classification`. -/
@[category API, AMS 5]
theorem matrix_mem_classification (m : Fin 3 → Fin 3 → ℕ)
    (hsum : ∑ i : Fin 3, ∑ j : Fin 3, m i j = 6)
    (hdiag : ∀ π : Equiv.Perm (Fin 3), 2 ≤ ∑ i : Fin 3, m i (π i)) :
    [m 0 0, m 0 1, m 0 2, m 1 0, m 1 1, m 1 2, m 2 0, m 2 1, m 2 2] ∈
      (comps 9 6).filter diagOK := by
  have d1 : 2 ≤ m 0 0 + m 1 1 + m 2 2 := by
    simpa [Fin.sum_univ_three] using hdiag 1
  have d2 : 2 ≤ m 0 0 + m 1 2 + m 2 1 := by
    simpa [Fin.sum_univ_three, Equiv.swap_apply_def] using hdiag (Equiv.swap 1 2)
  have d3 : 2 ≤ m 0 1 + m 1 0 + m 2 2 := by
    simpa [Fin.sum_univ_three, Equiv.swap_apply_def] using hdiag (Equiv.swap 0 1)
  have d4 : 2 ≤ m 0 1 + m 1 2 + m 2 0 := by
    simpa [Fin.sum_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      hdiag (Equiv.swap 0 1 * Equiv.swap 1 2)
  have d5 : 2 ≤ m 0 2 + m 1 0 + m 2 1 := by
    simpa [Fin.sum_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      hdiag (Equiv.swap 1 2 * Equiv.swap 0 1)
  have d6 : 2 ≤ m 0 2 + m 1 1 + m 2 0 := by
    simpa [Fin.sum_univ_three, Equiv.swap_apply_def] using hdiag (Equiv.swap 0 2)
  rw [List.mem_filter]
  constructor
  · rw [mem_comps]
    refine ⟨rfl, ?_⟩
    have hs : m 0 0 + m 0 1 + m 0 2 + (m 1 0 + m 1 1 + m 1 2) + (m 2 0 + m 2 1 + m 2 2) = 6 := by
      simpa [Fin.sum_univ_three] using hsum
    simp only [List.sum_cons, List.sum_nil]
    omega
  · simp only [diagOK, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- For `2 ≤ a ≤ 7`, `⌊a²/3⌋ < 3a - 3`: a 3-colourable graph on `a` vertices has fewer than
`3a - 3` edges, which excludes 6-edge-cut shores of sizes `2..7` in 6-regular `(4,1)`-graphs. -/
@[category API, AMS 5]
theorem turan_count_shore : ∀ a : ℕ, 2 ≤ a → a ≤ 7 → a ^ 2 / 3 < 3 * a - 3 := by
  intro a h2 h7
  interval_cases a <;> norm_num


end Erdos944
