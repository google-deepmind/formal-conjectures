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

# The city-building sequence $a(n)$

$a(n)$ is the height $h$ of the shortest building which can see exactly $h$ earlier buildings.
A building $a(j)$ "sees" an earlier building $a(i)$ if every intermediate building
$a(k), i < k < j$, has its top $(k, a(k))$ on or below the straight line joining
$(i, a(i))$ and $(j, a(j))$.

*References:*
- [A400000](https://oeis.org/A400000)
- [arxiv/0810.0920](https://arxiv.org/abs/0810.0920) *From time series to complex networks: the visibility graph* by Lacasa et al.
-/

@[expose] public section

namespace OeisA400000

/--
Let $p₀, p, p₁$ be points in the plane $ℕ × ℕ$, with increasing $x$-coordinates $x₀ < x < x₁$.
We say the point $p$ lies below (or on) the straight line joining points $p₀$ and $p₁$ whenever
the slope of the line from $p₀$ to $p$ is less than or equal to
the slope of the line from $p$ to $p₁$.
This is formalized using cross-multiplication to avoid division by zero.
-/
@[category API, AMS 11]
def point_on_or_below_line (p : ℕ × ℕ) (p₀ : ℕ × ℕ) (p₁ : ℕ × ℕ)
(_ : p₀.1 < p.1 := by omega) (_ : p.1 < p₁.1 := by omega) : Bool :=
  let (x₀, y₀) : (ℤ × ℤ) := (↑p₀.1, ↑p₀.2)
  let (x , y ) : (ℤ × ℤ) := (↑p.1, ↑p.2)
  let (x₁, y₁) : (ℤ × ℤ) := (↑p₁.1, ↑p₁.2)
  (x₁ - x) * (y - y₀) ≤ (x - x₀) * (y₁ - y)

/--
  Can building $n$ see building $m (m < n)$, given a list of building heights
  for all points $0 ≤ k ≤ n$ (and possibly beyond)?
  This happens exactly when every intermediate building $k$ with $m < k < n$
  has its top $(k, H[k])$ on or below the line joining $(m, H[m])$ and $(n, H[n])$.
-/
@[category API, AMS 11]
def is_visible (H : List ℕ) (m : ℕ) (n : ℕ)
(m_le_n : m < n := by omega) (Hl : H.length > n := by omega): Bool := decide (
  ∀ k (hk : k ∈ (Finset.Ioo m n)),
  have k_bound : m < k ∧ k < n := (Finset.mem_Ioo.1 hk)
  let p₀ := (m, H[m])
  let p  := (k, H[k])
  let p₁ := (n, H[n])
  have : p₀.1 < p.1 := k_bound.1
  have : p.1 < p₁.1 := k_bound.2
  point_on_or_below_line p p₀ p₁
)

/--
  Given a list of building heights for all points $0 ≤ k ≤ n$ (and possibly beyond),
  count how many buildings $k$ with $0 ≤ k < n$ can be seen from building $n$.
-/
@[category API, AMS 11]
def num_visible (H : List ℕ) (n : ℕ) (Hl : H.length > n := by simp): ℕ :=
  let k_set : Finset {x // x ∈ Finset.Ico 0 n} := (Finset.Ico 0 n).attach
  let k_is_visible : Finset.Ico 0 n → Prop := fun ⟨k, hk⟩ =>
    have : k < n := (Finset.mem_Ico.mp hk).2
    is_visible H k n
  (k_set.filter k_is_visible).card

/--
  Given a list of building heights and the height $h$ of the next building,
  count how many buildings can be seen from the next building.
-/
@[category API, AMS 11]
def num_visible_next (H : List ℕ) (h : ℕ): ℕ :=
  num_visible (H.concat h) H.length

/--
  Let $n = H.length$. The set of pairs $(h, #h)$ for heights $0 ≤ h ≤ n$, where
  $#h$ is the number of previous buildings $n$ could see if it has height $h$.
  Note building $n$ can see at most $n$ buildings.
-/
@[category API, AMS 11]
def num_visible_by_height (H : List ℕ) :=
  (Finset.Icc 0 H.length).map ⟨
    fun h => (h, num_visible_next H h),
    fun a b h => by injection h
  ⟩

/--
  The primary defining sequence `a`. Note we define it with the placeholder value of $0$ for now,
  in case the next term does not exist. The sequence does indeed continue forever.
-/
def a : ℕ -> ℕ
  | 0 => 0
  | n =>
    /- list of previous heights -/
    let H := (List.finRange n).map (fun (k : Fin n) => a k)
    /- $a(n)$ is the minimum $h$ such that $h = #h$ by definition. -/
    let num_visible_eq_height := (num_visible_by_height H).filter (fun (h, k) => h = k)
    /- It is not clear a priori that there are any such values $h$.
      This is indeed the case, as we will prove later.
      For now, assign the sequence a placeholder value of $0$. -/
    if h' : num_visible_eq_height.Nonempty
      then (num_visible_eq_height.inf' h' fun (k, _) => k)
      else 0

@[category API, AMS 11]
def prev_a_list (n : ℕ) := (List.finRange n).map (fun (k : Fin n) => a k)

@[category API, AMS 11]
lemma prev_nonempty_pos {n : ℕ} (npos : n > 0 := by omega) : prev_a_list n ≠ [] := by
  simp only [prev_a_list, ne_eq, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
  omega

@[category API, AMS 11]
lemma prev_is_visible (H : List ℕ) (n : ℕ) (npos : n > 0) (Hl : H.length > n := by simp) :
  is_visible H (n-1) n := by
    unfold is_visible
    rw [Bool.decide_iff]
    intro k hk
    simp at hk
    omega

@[category API, AMS 11]
lemma num_visible_zero_iff (H : List ℕ) (n : ℕ) (Hl : H.length > n := by simp) :
  (num_visible H n Hl) = 0 ↔ n = 0 := by
  constructor
  · unfold num_visible
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_attach, Bool.not_eq_true,
      forall_const, Subtype.forall, Nat.Ico_zero_eq_range, Finset.mem_range]
    intro hn
    by_contra
    have npos : n > 0 := by omega
    /- We should always be able to see the building directly before us. -/
    specialize hn (n-1) (by omega)
    let htrue := prev_is_visible H n npos Hl
    rw [hn] at htrue
    contradiction
  · intro hn
    unfold num_visible
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_attach, Bool.not_eq_true,
      forall_const, Subtype.forall, Nat.Ico_zero_eq_range, Finset.mem_range]
    intro a b
    omega -- No buildings precede building 0.

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by simp only [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
theorem a_14 : a 14 = 1 := by native_decide

@[category test, AMS 11]
theorem a_15 : a 15 = 10 := by native_decide

@[category test, AMS 11]
theorem a_16 : a 16 = 1 := by native_decide

/--
  The sequence does indeed go on forever, so the placeholder value of 0 is never used.
-/
@[category research solved, AMS 11]
theorem a_zero_iff (n : ℕ) : a n = 0 ↔ n = 0 := by
  sorry

/--
Conjecture: limsup_{n → ∞} (Sum_{k=1..n} a(k))/n ≤ 3
$a(n)$ is the backward degree of node n in the natural visibility graph of the sequence itself
(Lacasa et al., 2008), with collinear points counted as visible: each new term is the least
value equal to the number of earlier terms it is connected to.
Consequently, $Sum_{k=1..n} a(k)$ is the number of edges of the natural visibility graph of the
first $n$ terms, and the conjecture... is equivalent to the asymptotic mean degree of this
graph being at most 6. - Francisco J. Muñoz, Oct 26 2026
-/
@[category research open, AMS 11]
theorem conjecture :
  let f := (fun n : ℕ => (∑ k ∈ Finset.range n, a k : ℝ) / (n : ℝ))
  Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f
  ∧ Filter.limsup f Filter.atTop ≤ (3 : ℝ) := by
    sorry

end OeisA400000
