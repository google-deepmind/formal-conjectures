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
# Erdős Problem 76

*References:*
- [erdosproblems.com/76](https://www.erdosproblems.com/76)
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81-85.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
- [GrLe20] Gruslys, Vytautas and Letzter, Shoham, *Monochromatic triangle packings in red-blue
  graphs*. arXiv:2008.05311 (2020); Combin. Probab. Comput. **31** (2022), 994-1027.

## Formalization choices

* The vertex set of $K_n$ is `Fin n` and an edge is an element of `Sym2 (Fin n)`.
  A $2$-colouring is any function `c : Sym2 (Fin n) → Bool`. Its values on the diagonal
  `s(a, a)`, which are not edges, are irrelevant.
* A triangle is a $3$-element vertex set $\{a, b, d\}$. It is monochromatic when its three
  edges have the same colour.
* Two distinct triangles are edge-disjoint iff they share at most one vertex.
* "At least $(1 + o(1)) n^2 / 12$" means: for every $\varepsilon > 0$ and all sufficiently
  large $n$, every colouring admits such a family of size at least $(1 - \varepsilon) n^2 / 12$.
-/

@[expose] public section

namespace Erdos76

/-- `t` is a monochromatic triangle of $K_n$ under the colouring `c`. -/
def IsMonoTriangle {n : ℕ} (c : Sym2 (Fin n) → Bool) (t : Finset (Fin n)) : Prop :=
  ∃ a b d : Fin n, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ t = {a, b, d} ∧
    c s(a, b) = c s(a, d) ∧ c s(a, b) = c s(b, d)

/-- `T` is a family of pairwise edge-disjoint monochromatic triangles under `c`. -/
def IsEdgeDisjointMonoTriangles {n : ℕ} (c : Sym2 (Fin n) → Bool)
    (T : Finset (Finset (Fin n))) : Prop :=
  (∀ t ∈ T, IsMonoTriangle c t) ∧
    (T : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1)

/--
Is it true that in any $2$-colouring of the edges of $K_n$ there must exist at least
$$(1+o(1))\frac{n^2}{12}$$
many edge-disjoint monochromatic triangles?

Conjectured by Erdős, Faudree, and Ordman. The answer is yes, proved by Gruslys and Letzter
[GrLe20].
-/
@[category research solved, AMS 5]
theorem erdos_76 :
    answer(True) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ c : Sym2 (Fin n) → Bool,
        ∃ T : Finset (Finset (Fin n)), IsEdgeDisjointMonoTriangles c T ∧
          (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (T.card : ℝ) := by
  sorry

/-- The half-split colouring: an edge is `true` (blue) iff both endpoints lie in the
same half $\{i < n/2\}$ or $\{i \ge n/2\}$. -/
def halfColouring (n : ℕ) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun a b => decide ((a.val < n / 2) ↔ (b.val < n / 2)), by
    intro a b; simp only [decide_eq_decide]; exact Iff.comm⟩

@[category API, AMS 5]
private lemma mono_half_subset {n : ℕ} {t : Finset (Fin n)}
    (ht : IsMonoTriangle (halfColouring n) t) :
    t ⊆ Finset.univ.filter (fun i : Fin n => i.val < n / 2) ∨
      t ⊆ Finset.univ.filter (fun i : Fin n => ¬ i.val < n / 2) := by
  obtain ⟨a, b, d, -, -, -, rfl, h1, h2⟩ := ht
  simp only [halfColouring, Sym2.lift_mk, decide_eq_decide] at h1 h2
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases ha : a.val < n / 2 <;> by_cases hb : b.val < n / 2 <;>
    by_cases hd : d.val < n / 2 <;> simp_all

@[category API, AMS 5]
private lemma mono_edges_card {n : ℕ} {c : Sym2 (Fin n) → Bool} {t : Finset (Fin n)}
    (ht : IsMonoTriangle c t) : (t.offDiag.image Sym2.mk.uncurry).card = 3 := by
  obtain ⟨a, b, d, hab, had, hbd, rfl, -, -⟩ := ht
  rw [Sym2.card_image_offDiag, Finset.card_insert_of_notMem (by simp [hab, had]),
    Finset.card_pair hbd]
  rfl

@[category API, AMS 5]
private lemma edges_disjoint {n : ℕ} {s t : Finset (Fin n)} (h : (s ∩ t).card ≤ 1) :
    Disjoint (s.offDiag.image Sym2.mk.uncurry) (t.offDiag.image Sym2.mk.uncurry) := by
  rw [Finset.disjoint_left]
  rintro e he he'
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨⟨x', y'⟩, hxy', he2⟩ := Finset.mem_image.mp he'
  simp only [Finset.mem_offDiag] at hxy hxy'
  simp only [Function.uncurry_apply_pair] at he2
  have hx : x ∈ t ∧ y ∈ t := by
    rcases Sym2.eq_iff.mp he2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxy'.1, hxy'.2.1⟩
    · exact ⟨hxy'.2.1, hxy'.1⟩
  have : ({x, y} : Finset (Fin n)) ⊆ s ∩ t := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [hxy.1, hxy.2.1, hx.1, hx.2]
  have := Finset.card_le_card this
  rw [Finset.card_pair hxy.2.2] at this
  omega

@[category API, AMS 5]
private lemma card_filter_lt (n k : ℕ) (h : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  rw [← Finset.card_map Fin.valEmbedding, ← Finset.card_range k]
  congr 1; ext x; simp; constructor
  · rintro ⟨a, h1, rfl⟩; exact h1
  · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩

@[category API, AMS 5]
private lemma card_filter_not_lt (n k : ℕ) :
    (Finset.univ.filter (fun i : Fin n => ¬ i.val < k)).card = n - k := by
  rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico k n]
  congr 1; ext x; simp; constructor
  · rintro ⟨a, h1, rfl⟩; omega
  · intro hx; exact ⟨⟨x, by omega⟩, by simp; omega, rfl⟩

@[category API, AMS 5]
private lemma four_choose_le (n : ℕ) :
    4 * ((n / 2).choose 2 + (n - n / 2).choose 2) ≤ n ^ 2 := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have : 2 * k / 2 = k := by omega
    rw [this, show 2 * k - k = k by omega]
    have := Nat.div_mul_le_self (k * (k - 1)) 2
    have := Nat.mul_le_mul_left k (Nat.sub_le k 1)
    nlinarith
  · have : (2 * k + 1) / 2 = k := by omega
    rw [this, show 2 * k + 1 - k = k + 1 by omega]
    have := Nat.div_mul_le_self (k * (k - 1)) 2
    have := Nat.div_mul_le_self ((k + 1) * (k + 1 - 1)) 2
    have := Nat.mul_le_mul_left k (Nat.sub_le k 1)
    simp only [Nat.add_sub_cancel] at *
    nlinarith

/--
The constant $1/12$ is best possible, as witnessed by dividing the vertices of $K_n$ into two
equal parts and colouring all edges between the parts red and all edges inside the parts blue:
any family of edge-disjoint monochromatic triangles then has at most $n^2/12$ members.
-/
@[category research solved, AMS 5]
theorem erdos_76.variants.sharp (n : ℕ) :
    ∃ c : Sym2 (Fin n) → Bool, ∀ T : Finset (Finset (Fin n)),
      IsEdgeDisjointMonoTriangles c T → 12 * T.card ≤ n ^ 2 := by
  refine ⟨halfColouring n, fun T ⟨hmono, hdisj⟩ => ?_⟩
  set A := Finset.univ.filter (fun i : Fin n => i.val < n / 2)
  set B := Finset.univ.filter (fun i : Fin n => ¬ i.val < n / 2)
  have hcard : (T.biUnion fun t => t.offDiag.image Sym2.mk.uncurry).card = 3 * T.card := by
    rw [Finset.card_biUnion (fun s hs t ht hst => edges_disjoint (hdisj hs ht hst)),
      Finset.sum_congr rfl (fun t ht => mono_edges_card (hmono t ht))]
    simp [mul_comm]
  have hsub : (T.biUnion fun t => t.offDiag.image Sym2.mk.uncurry) ⊆
      A.offDiag.image Sym2.mk.uncurry ∪ B.offDiag.image Sym2.mk.uncurry := by
    intro e he
    obtain ⟨t, ht, he⟩ := Finset.mem_biUnion.mp he
    rcases mono_half_subset (hmono t ht) with h | h
    · exact Finset.mem_union_left _
        (Finset.image_subset_image (Finset.offDiag_mono h) he)
    · exact Finset.mem_union_right _
        (Finset.image_subset_image (Finset.offDiag_mono h) he)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hcard, Sym2.card_image_offDiag, Sym2.card_image_offDiag,
    card_filter_lt n (n / 2) (Nat.div_le_self n 2), card_filter_not_lt] at h1
  have := four_choose_le n
  omega

/--
In [Er97d] Erdős also asks for a lower bound for the count of edge-disjoint monochromatic
triangles in a single colour (the colour chosen to maximise this quantity), and speculates that
the answer is $\geq cn^2$ for some constant $c > 1/24$.
-/
@[category research open, AMS 5]
theorem erdos_76.variants.single_colour :
    answer(sorry) ↔
      ∃ C : ℝ, 1 / 24 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ c : Sym2 (Fin n) → Bool,
        ∃ col : Bool, ∃ T : Finset (Finset (Fin n)), IsEdgeDisjointMonoTriangles c T ∧
          (∀ t ∈ T, ∀ a ∈ t, ∀ b ∈ t, a ≠ b → c s(a, b) = col) ∧
          C * (n : ℝ) ^ 2 ≤ (T.card : ℝ) := by
  sorry

end Erdos76
