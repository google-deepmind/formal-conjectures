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

Skottova and Steiner [SkSt25] proved that every $(4,1)$-graph (a $4$-vertex-critical
graph with no critical edge) has minimum degree and edge-connectivity at least $6$, and
asked (their Problem 5.2) whether a $6$-regular $(4,1)$-graph exists. The following are
machine-checked cores of verified computational results on that subproblem
(2026): there is no $6$-regular $4$-vertex-critical graph on $n \le 15$ except a unique
one on $n = 13$ (which has critical edges), so any $6$-regular $(4,1)$-graph has at
least $16$ vertices; and in any $6$-regular $(4,1)$-graph every $6$-edge-cut is either
a vertex star or has both shores of size at least $15$ (hence such a graph on
$n \le 29$ vertices is super-$6$-edge-connected).

* `singleton_edge_critical`: the recolouring core of the singleton lemma — if a
  $3$-colouring of $G - v$ gives colour $c$ to exactly one neighbour $u$ of $v$, the
  extension by $v \mapsto c$ is proper on every edge except $uv$ (hence $uv$ is
  critical in a $4$-vertex-critical graph). Axiom-free.
* `cut_matrix_classification` (with the enumeration-completeness lemma `mem_comps`):
  exactly $21$ of the $3 	imes 3$ nonnegative matrices with entry sum $6$ have all six
  permutation-diagonal sums at least $2$ — the exact equality case of the
  Skottova–Steiner cut bound. `matrix_mem_classification` is the bridge from the
  genuine matrix form.
* `cut_row_forcing`: among those $21$ matrices, row sums $(3,3,0)$ force both nonzero
  rows to be $(1,1,1)$ and row sums $(6,0,0)$ force the nonzero row to be $(2,2,2)$.
  These two equality cases drive a stronger structural result: no shore of a
  nontrivial $6$-edge-cut in a $6$-regular $(4,1)$-graph induces a bipartite graph,
  and a shore whose deficiency is concentrated on two vertices forces those two
  vertices to receive equal colours in every $3$-colouring.
* `turan_count_shore`: the numeric core excluding $6$-cut shores of size $2,\dots,7$.

[SkSt25] Skottova, Ema and Steiner, Raphael, Critical edge sets in vertex-critical
graphs. arXiv:2508.08703 (2025)

A self-contained write-up of these computational results, with full proofs, code,
certificates, and these Lean cores as ancillary files, is: A. Ferudun, Exact
$6$-cut rigidity and small-order superconnectivity for the $6$-regular case of
Dirac's $k=4$ problem, arXiv:2606.18462 (2026).
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
the exact equality case of the Skottova–Steiner 6-edge-cut bound for `(4,1)`-graphs. -/
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

/-- Row-forcing predicate on a row-major 3×3 matrix `[a,b,c; d,e,f; g,h,i]`: in the `(3,3,0)`
row-sum case both nonzero rows must equal `(1,1,1)`; in the `(6,0,0)` row-sum case the nonzero
row must equal `(2,2,2)`. -/
def rowForcing : List ℕ → Bool
  | [a, b, c, d, e, f, g, h, i] =>
      let r0 := [a, b, c]; let r1 := [d, e, f]; let r2 := [g, h, i]
      let s0 := a + b + c; let s1 := d + e + f; let s2 := g + h + i
      let is330 := (s0 == 0 && s1 == 3 && s2 == 3) || (s0 == 3 && s1 == 0 && s2 == 3) ||
                   (s0 == 3 && s1 == 3 && s2 == 0)
      let is600 := (s0 == 6 && s1 == 0 && s2 == 0) || (s0 == 0 && s1 == 6 && s2 == 0) ||
                   (s0 == 0 && s1 == 0 && s2 == 6)
      let ok330 := !is330 ||
        ((s0 == 0 || r0 == [1, 1, 1]) && (s1 == 0 || r1 == [1, 1, 1]) &&
         (s2 == 0 || r2 == [1, 1, 1]))
      let ok600 := !is600 ||
        ((!(s0 == 6) || r0 == [2, 2, 2]) && (!(s1 == 6) || r1 == [2, 2, 2]) &&
         (!(s2 == 6) || r2 == [2, 2, 2]))
      ok330 && ok600
  | _ => true

set_option maxRecDepth 100000 in
/-- Every valid 6-edge-cut matrix obeys the row-forcing law: if the deficiency-weighted row-sum
vector is a permutation of `(3,3,0)` then both nonzero rows are `(1,1,1)` (each cut triple is
rainbow under every partner colouring), and if it is `(6,0,0)` then the nonzero row is `(2,2,2)`
(the six cut endpoints split `2+2+2`). These are the two equality cases driving the exclusion of
bipartite and concentrated shores. -/
@[category API, AMS 5]
theorem cut_row_forcing : ((comps 9 6).filter diagOK).all rowForcing = true := by decide

/-- For `2 ≤ a ≤ 7`, `⌊a²/3⌋ < 3a - 3`: a 3-colourable graph on `a` vertices has fewer than
`3a - 3` edges, which excludes 6-edge-cut shores of sizes `2..7` in 6-regular `(4,1)`-graphs. -/
@[category API, AMS 5]
theorem turan_count_shore : ∀ a : ℕ, 2 ≤ a → a ≤ 7 → a ^ 2 / 3 < 3 * a - 3 := by
  intro a h2 h7
  interval_cases a <;> norm_num


/-
## Zero-budget identities for the deficiency-6 shore analysis

In the structural analysis of $6$-edge-cut shores of a $6$-regular $(4,1)$-graph, the
shore graph $H$ has $\Delta(H) \le 6$ and total deficiency $\sum_x (6 - \deg x) = 6$.
For a full vertex $v$ ($\deg v = 6$) whose deletion admits a proper $3$-colouring with
colour counts $(2,2,2)$ on $N(v)$ (a *deletion-unfrozen* vertex), exact double counting
constrains the colour classes. With $p = |IJ|$ (union of the two non-$k$ classes off
$v$), $q = |K|$ (the $k$-class off $v$), $B_k$ the deficiency mass on $K$, and $s_{IJ}$
twice the number of edges internal to $IJ$:

* `zero_budget_edge_formula` (L1): $s_{IJ} = 6p - 6q + 2B_k - 8$.
* `charge_identity` (L2): $6p - s_{IJ} = 6q + 8 - 2B_k$; the left side equals
  $\sum_C \kappa(C)$ over the components $C$ of $H[IJ]$, where
  $\kappa(C) = 6|C| - 2e(C)$, so L2 is the component charge identity.
* `double_sum_even`: every internal indicator double sum is even ($\kappa$-parity).

These are the arithmetic core of the zero-budget accounting step in the verified
computational programme on [SkSt25] Problem 5.2 (2026).
-/

namespace ZeroBudget

open Finset

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (c : V → Fin 3) (v : V) (k : Fin 3)

/-- The union of the two non-`k` colour classes, excluding `v`. -/
def IJ : Finset V := univ.filter fun x => x ≠ v ∧ c x ≠ k

/-- The `k`-colour class, excluding `v`. -/
def Kcl : Finset V := univ.filter fun x => x ≠ v ∧ c x = k

/-- Twice the number of edges of `G` with both endpoints in `IJ`,
as an adjacency-indicator double sum (over ℤ). -/
def sIJ : ℤ := ∑ x ∈ IJ c v k, ∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0)

@[category API, AMS 5]
lemma mem_IJ {x : V} : x ∈ IJ c v k ↔ x ≠ v ∧ c x ≠ k := by
  simp [IJ]

@[category API, AMS 5]
lemma mem_Kcl {x : V} : x ∈ Kcl c v k ↔ x ≠ v ∧ c x = k := by
  simp [Kcl]

/-- `{v}`, `IJ`, `Kcl` partition the vertex set: sums over `univ` split accordingly. -/
@[category API, AMS 5]
lemma sum_univ_split (f : V → ℤ) :
    ∑ y, f y = f v + (∑ y ∈ IJ c v k, f y) + ∑ y ∈ Kcl c v k, f y := by
  have hdisj : Disjoint (IJ c v k) (Kcl c v k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_IJ] at ha
    rw [mem_Kcl] at hb
    exact ha.2 hb.2
  have hv : v ∉ IJ c v k ∪ Kcl c v k := by
    simp [mem_IJ, mem_Kcl]
  have hall : ∀ x : V, x ∈ insert v (IJ c v k ∪ Kcl c v k) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_union, mem_IJ, mem_Kcl]
    by_cases hx : x = v
    · exact Or.inl hx
    · by_cases hc : c x = k
      · exact Or.inr (Or.inr ⟨hx, hc⟩)
      · exact Or.inr (Or.inl ⟨hx, hc⟩)
  have huniv : (univ : Finset V) = insert v (IJ c v k ∪ Kcl c v k) :=
    (Finset.eq_univ_iff_forall.mpr hall).symm
  rw [huniv, Finset.sum_insert hv, Finset.sum_union hdisj]
  ring

omit [DecidableEq V] in
/-- Degree as an adjacency-indicator sum over all vertices (in ℤ). -/
lemma degree_eq_sum (x : V) :
    (G.degree x : ℤ) = ∑ y, (if G.Adj x y then (1 : ℤ) else 0) := by
  have h : G.neighborFinset x = univ.filter fun y => G.Adj x y := by
    ext y
    simp [SimpleGraph.mem_neighborFinset]
  rw [Finset.sum_boole, ← h]
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Indicator symmetry from adjacency symmetry. -/
lemma ite_adj_comm (x y : V) :
    (if G.Adj x y then (1 : ℤ) else 0) = if G.Adj y x then (1 : ℤ) else 0 := by
  by_cases h : G.Adj x y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- `Kcl` is independent in `G` (properness of `c` off `v`). -/
@[category API, AMS 5]
lemma sum_Kcl_Kcl_eq_zero
    (hproper : ∀ x y, G.Adj x y → x ≠ v → y ≠ v → c x ≠ c y) :
    ∑ x ∈ Kcl c v k, ∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
  rw [mem_Kcl] at hx hy
  have hnadj : ¬ G.Adj x y := fun hadj =>
    hproper x y hadj hx.1 hy.1 (hx.2.trans hy.2.symm)
  rw [if_neg hnadj]

/-- Cross-edge double count: `Kcl→IJ` indicator sum equals `IJ→Kcl` indicator sum. -/
@[category API, AMS 5]
lemma cross_symm :
    ∑ x ∈ Kcl c v k, ∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0)
      = ∑ x ∈ IJ c v k, ∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ite_adj_comm G y x

/-- `C = 2`: the vertex `v` has exactly `2` neighbours in `Kcl`. -/
@[category API, AMS 5]
lemma sum_C
    (hcnt : ∀ t : Fin 3, ((G.neighborFinset v).filter (fun u => c u = t)).card = 2) :
    ∑ x ∈ Kcl c v k, (if G.Adj x v then (1 : ℤ) else 0) = 2 := by
  have h1 : ∑ x ∈ Kcl c v k, (if G.Adj x v then (1 : ℤ) else 0)
      = ∑ x ∈ Kcl c v k, (if G.Adj v x then (1 : ℤ) else 0) :=
    Finset.sum_congr rfl fun x _ => ite_adj_comm G x v
  have h2 : (Kcl c v k).filter (fun x => G.Adj v x)
      = (G.neighborFinset v).filter (fun u => c u = k) := by
    ext x
    simp only [Finset.mem_filter, mem_Kcl, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hck⟩, hadj⟩
      exact ⟨hadj, hck⟩
    · rintro ⟨hadj, hck⟩
      exact ⟨⟨hadj.ne', hck⟩, hadj⟩
  rw [h1, Finset.sum_boole, h2, hcnt k]
  norm_num

/-- `A = 4`: the vertex `v` has exactly `4` neighbours in `IJ`
(its `6` neighbours minus the `2` in the `k`-class). -/
@[category API, AMS 5]
lemma sum_A (b : V → ℕ)
    (hdeg : ∀ x, G.degree x + b x = 6) (hbv : b v = 0)
    (hcnt : ∀ t : Fin 3, ((G.neighborFinset v).filter (fun u => c u = t)).card = 2) :
    ∑ x ∈ IJ c v k, (if G.Adj x v then (1 : ℤ) else 0) = 4 := by
  have h1 : ∑ x ∈ IJ c v k, (if G.Adj x v then (1 : ℤ) else 0)
      = ∑ x ∈ IJ c v k, (if G.Adj v x then (1 : ℤ) else 0) :=
    Finset.sum_congr rfl fun x _ => ite_adj_comm G x v
  have h2 : (IJ c v k).filter (fun x => G.Adj v x)
      = (G.neighborFinset v).filter (fun u => ¬ c u = k) := by
    ext x
    simp only [Finset.mem_filter, mem_IJ, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hck⟩, hadj⟩
      exact ⟨hadj, hck⟩
    · rintro ⟨hadj, hck⟩
      exact ⟨⟨hadj.ne', hck⟩, hadj⟩
  have hdv : (G.neighborFinset v).card = 6 := by
    have h := hdeg v
    rw [hbv, add_zero] at h
    exact h
  have h3 : ((G.neighborFinset v).filter (fun u => ¬ c u = k)).card = 4 := by
    have h4 : ((G.neighborFinset v).filter (fun u => c u = k)).card
        + ((G.neighborFinset v).filter (fun u => ¬ c u = k)).card
        = (G.neighborFinset v).card :=
      Finset.card_filter_add_card_filter_not (fun u => c u = k)
    rw [hcnt k, hdv] at h4
    omega
  rw [h1, Finset.sum_boole, h2, h3]
  norm_num

/-- **L1, the zero-budget edge formula.**
`sIJ = 6·|IJ| − 6·|Kcl| + 2·(∑_{x ∈ Kcl} b x) − 8`,
where `sIJ` is twice the number of `G`-edges internal to `IJ`. -/
@[category API, AMS 5]
theorem zero_budget_edge_formula (b : V → ℕ)
    (hdeg : ∀ x, G.degree x + b x = 6)
    (hb6 : ∑ x, b x = 6)
    (hbv : b v = 0)
    (hproper : ∀ x y, G.Adj x y → x ≠ v → y ≠ v → c x ≠ c y)
    (hcnt : ∀ t : Fin 3, ((G.neighborFinset v).filter (fun u => c u = t)).card = 2) :
    sIJ G c v k
      = 6 * ((IJ c v k).card : ℤ) - 6 * ((Kcl c v k).card : ℤ)
        + 2 * ((∑ x ∈ Kcl c v k, b x : ℕ) : ℤ) - 8 := by
  -- (1) Sum of degrees over IJ = sIJ + E + A, with A = 4.
  have hIJdeg : ∑ x ∈ IJ c v k, (G.degree x : ℤ)
      = (∑ x ∈ IJ c v k, ∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0))
        + (∑ x ∈ IJ c v k, ∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0)) + 4 := by
    have hsplit : ∀ x ∈ IJ c v k, (G.degree x : ℤ)
        = (if G.Adj x v then (1 : ℤ) else 0)
          + (∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0))
          + (∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0)) := by
      intro x _
      rw [degree_eq_sum G x]
      exact sum_univ_split c v k _
    rw [Finset.sum_congr rfl hsplit]
    simp only [Finset.sum_add_distrib]
    rw [sum_A G c v k b hdeg hbv hcnt]
    ring
  -- (2) Sum of degrees over Kcl = E + C, with C = 2 (Kcl independent).
  have hKdeg : ∑ x ∈ Kcl c v k, (G.degree x : ℤ)
      = (∑ x ∈ IJ c v k, ∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0)) + 2 := by
    have hsplit : ∀ x ∈ Kcl c v k, (G.degree x : ℤ)
        = (if G.Adj x v then (1 : ℤ) else 0)
          + (∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0))
          + (∑ y ∈ Kcl c v k, (if G.Adj x y then (1 : ℤ) else 0)) := by
      intro x _
      rw [degree_eq_sum G x]
      exact sum_univ_split c v k _
    rw [Finset.sum_congr rfl hsplit]
    simp only [Finset.sum_add_distrib]
    rw [sum_C G c v k hcnt, sum_Kcl_Kcl_eq_zero G c v k hproper, cross_symm G c v k]
    ring
  -- (5) Degree sums via the deficiency hypothesis.
  have hdegIJ : ∑ x ∈ IJ c v k, (G.degree x : ℤ)
      = 6 * ((IJ c v k).card : ℤ) - ∑ x ∈ IJ c v k, (b x : ℤ) := by
    have hstep : ∀ x ∈ IJ c v k, (G.degree x : ℤ) = 6 - (b x : ℤ) := by
      intro x _
      have h := hdeg x
      omega
    rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hdegK : ∑ x ∈ Kcl c v k, (G.degree x : ℤ)
      = 6 * ((Kcl c v k).card : ℤ) - ∑ x ∈ Kcl c v k, (b x : ℤ) := by
    have hstep : ∀ x ∈ Kcl c v k, (G.degree x : ℤ) = 6 - (b x : ℤ) := by
      intro x _
      have h := hdeg x
      omega
    rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  -- (5') Budget split: B_IJ + B_K = 6 (using b v = 0).
  have hbsum : (∑ x ∈ IJ c v k, (b x : ℤ)) + (∑ x ∈ Kcl c v k, (b x : ℤ)) = 6 := by
    have h := sum_univ_split c v k (fun x => (b x : ℤ))
    simp only [hbv, Nat.cast_zero, zero_add] at h
    have h6 : (∑ x : V, (b x : ℤ)) = 6 := by exact_mod_cast hb6
    rw [h6] at h
    linarith [h]
  -- (6) Combine.
  have hcast : ((∑ x ∈ Kcl c v k, b x : ℕ) : ℤ) = ∑ x ∈ Kcl c v k, (b x : ℤ) :=
    Nat.cast_sum _ _
  have hsIJ : sIJ G c v k
      = ∑ x ∈ IJ c v k, ∑ y ∈ IJ c v k, (if G.Adj x y then (1 : ℤ) else 0) := rfl
  rw [hsIJ, hcast]
  linarith [hIJdeg, hKdeg, hdegIJ, hdegK, hbsum]

/-- **L2, the charge identity** (arithmetic form): follows from L1.
`6·|IJ| − sIJ = 6·|Kcl| + 8 − 2·(∑_{x ∈ Kcl} b x)`. The left side equals
`∑_C κ(C)` over the components `C` of the graph induced on `IJ`. -/
@[category API, AMS 5]
theorem charge_identity (b : V → ℕ)
    (hdeg : ∀ x, G.degree x + b x = 6)
    (hb6 : ∑ x, b x = 6)
    (hbv : b v = 0)
    (hproper : ∀ x y, G.Adj x y → x ≠ v → y ≠ v → c x ≠ c y)
    (hcnt : ∀ t : Fin 3, ((G.neighborFinset v).filter (fun u => c u = t)).card = 2) :
    6 * ((IJ c v k).card : ℤ) - sIJ G c v k
      = 6 * ((Kcl c v k).card : ℤ) + 8 - 2 * ((∑ x ∈ Kcl c v k, b x : ℕ) : ℤ) := by
  have h := zero_budget_edge_formula G c v k b hdeg hb6 hbv hproper hcnt
  linarith

omit [Fintype V] in
/-- κ-parity: any internal indicator double sum is even,
i.e. `s_W = 2·e_W` for some `e_W` — by symmetry and irreflexivity of `Adj`. -/
@[category API, AMS 5]
theorem double_sum_even (W : Finset V) :
    ∃ e : ℤ, ∑ x ∈ W, ∑ y ∈ W, (if G.Adj x y then (1 : ℤ) else 0) = 2 * e := by
  induction W using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a W ha ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + ∑ y ∈ W, (if G.Adj a y then (1 : ℤ) else 0), ?_⟩
    have h1 : ∑ y ∈ insert a W, (if G.Adj a y then (1 : ℤ) else 0)
        = ∑ y ∈ W, (if G.Adj a y then (1 : ℤ) else 0) := by
      rw [Finset.sum_insert ha, if_neg (G.irrefl), zero_add]
    have h2 : ∀ x ∈ W, (∑ y ∈ insert a W, (if G.Adj x y then (1 : ℤ) else 0))
        = (if G.Adj x a then (1 : ℤ) else 0)
          + ∑ y ∈ W, (if G.Adj x y then (1 : ℤ) else 0) :=
      fun x _ => Finset.sum_insert ha
    have h3 : ∑ x ∈ W, (if G.Adj x a then (1 : ℤ) else 0)
        = ∑ y ∈ W, (if G.Adj a y then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl fun x _ => ite_adj_comm G x a
    rw [Finset.sum_insert ha, h1, Finset.sum_congr rfl h2]
    simp only [Finset.sum_add_distrib]
    rw [h3, he]
    ring

end ZeroBudget

end Erdos944
