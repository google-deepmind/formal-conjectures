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
public import FormalConjectures.ErdosProblems.«101»

/-!
# Erdős Problem 669

*References:*
- [erdosproblems.com/669](https://www.erdosproblems.com/669)
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
-/

@[expose] public section

open Filter
open scoped Topology EuclideanGeometry

namespace Erdos669

/--
The set of lines in $\mathbb{R}^2$ containing at least $k$ points of $S$. It is the analogue of
`Erdos101.linesWithPointsFor`, which asks for exactly $k$ points. Only lines spanned by two
distinct points of $S$ are counted, so the definition is meant for $k \geq 2$.
-/
noncomputable def linesWithAtLeastPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | k ≤ (↑L ∩ S).ncard }

/--
The set of numbers of distinct lines through at least $k$ points, taken over all sets of $n$
points in $\mathbb{R}^2$.
-/
noncomputable def lineCountsAtLeast (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧ (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard = m}

/--
The set of numbers of distinct lines through exactly $k$ points, taken over all sets of $n$
points in $\mathbb{R}^2$.
-/
noncomputable def lineCountsExactly (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧ (Erdos101.linesWithPointsFor k (S : Set ℝ²)).ncard = m}

/-- A set of lines, each spanned by two points of `S`, has at most `S.card ^ 2` elements. -/
@[category API, AMS 52]
private lemma ncard_le_sq (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²))
    (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) : T.ncard ≤ S.card ^ 2 := by
  have hfin : ((S : Set ℝ²) ×ˢ (S : Set ℝ²)).Finite := S.finite_toSet.prod S.finite_toSet
  have hcard : ((S : Set ℝ²) ×ˢ (S : Set ℝ²)).ncard = S.card ^ 2 := by
    rw [Set.ncard_prod, Set.ncard_coe_finset, sq]
  have hsub : T ⊆ (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2}) ''
      ((S : Set ℝ²) ×ˢ (S : Set ℝ²)) := by
    intro L hL
    obtain ⟨p, hp, q, hq, rfl⟩ := hT L hL
    exact ⟨(p, q), Set.mk_mem_prod (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq), rfl⟩
  exact (Set.ncard_le_ncard hsub (hfin.image _)).trans
    ((Set.ncard_image_le hfin).trans hcard.le)

/--
The counts are bounded: a line through two or more points of an $n$-point set is spanned by an
ordered pair of its points, and there are at most $n^2$ ordered pairs. The set is also nonempty,
since $n$-point sets exist, so the `sSup` in `Erdos669.maxLinesAtLeast` is attained.
-/
@[category test, AMS 52]
theorem lineCountsAtLeast_bddAbove (k n : ℕ) : BddAbove (lineCountsAtLeast k n) := by
  refine ⟨n ^ 2, ?_⟩
  rintro _ ⟨S, rfl, rfl⟩
  refine ncard_le_sq S _ ?_
  rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
  exact ⟨p, Finset.mem_coe.1 hp, q, Finset.mem_coe.1 hq, rfl⟩

/--
The same bound for lines through exactly $k$ points, so the `sSup` in `Erdos669.maxLinesExactly`
is attained as well.
-/
@[category test, AMS 52]
theorem lineCountsExactly_bddAbove (k n : ℕ) : BddAbove (lineCountsExactly k n) := by
  refine ⟨n ^ 2, ?_⟩
  rintro _ ⟨S, rfl, rfl⟩
  refine ncard_le_sq S _ ?_
  rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
  exact ⟨p, Finset.mem_coe.1 hp, q, Finset.mem_coe.1 hq, rfl⟩

/--
A line through exactly $k$ points of $S$ is a line through at least $k$ points of $S$.
-/
@[category test, AMS 52]
theorem linesWithPointsFor_subset_linesWithAtLeastPointsFor (k : ℕ) (S : Set ℝ²) :
    Erdos101.linesWithPointsFor k S ⊆ linesWithAtLeastPointsFor k S := by
  rintro L ⟨hL, hk⟩
  exact ⟨hL, hk.ge⟩

/--
$F_k(n)$: the largest number of distinct lines passing through at least $k$ of the points, over
all sets of $n$ points in $\mathbb{R}^2$. This is the least $m$ such that any $n$ points have at
most $m$ such lines. See `Erdos669.lineCountsAtLeast_bddAbove`.
-/
noncomputable def maxLinesAtLeast (k n : ℕ) : ℕ :=
  sSup (lineCountsAtLeast k n)

/--
$f_k(n)$: the largest number of distinct lines passing through exactly $k$ of the points, over
all sets of $n$ points in $\mathbb{R}^2$. This is the least $m$ such that any $n$ points have at
most $m$ such lines. See `Erdos669.lineCountsExactly_bddAbove`.
-/
noncomputable def maxLinesExactly (k n : ℕ) : ℕ :=
  sSup (lineCountsExactly k n)

/--
Let $F_k(n)$ be minimal such that for any $n$ points in $\mathbb{R}^2$ there exist at most
$F_k(n)$ many distinct lines passing through at least $k$ of the points, and $f_k(n)$ similarly
but with lines passing through exactly $k$ points.

Estimate $f_k(n)$ and $F_k(n)$ - in particular, determine $\lim F_k(n)/n^2$ and
$\lim f_k(n)/n^2$.

This part asks for $\lim F_k(n)/n^2$, as a function `L` of $k \geq 3$ (the case $k = 2$ is
trivial). The statement includes that the limit exists.
-/
@[category research open, AMS 52]
theorem erdos_669.parts.i :
    let L : ℕ → ℝ := answer(sorry)
    ∀ k : ℕ, 3 ≤ k →
      Tendsto (fun n : ℕ => (maxLinesAtLeast k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (L k)) := by
  sorry

/--
Let $F_k(n)$ be minimal such that for any $n$ points in $\mathbb{R}^2$ there exist at most
$F_k(n)$ many distinct lines passing through at least $k$ of the points, and $f_k(n)$ similarly
but with lines passing through exactly $k$ points.

Estimate $f_k(n)$ and $F_k(n)$ - in particular, determine $\lim F_k(n)/n^2$ and
$\lim f_k(n)/n^2$.

This part asks for $\lim f_k(n)/n^2$, as a function `L` of $k \geq 3$ (the case $k = 2$ is
trivial). The statement includes that the limit exists.
-/
@[category research open, AMS 52]
theorem erdos_669.parts.ii :
    let L : ℕ → ℝ := answer(sorry)
    ∀ k : ℕ, 3 ≤ k →
      Tendsto (fun n : ℕ => (maxLinesExactly k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (L k)) := by
  sorry

/--
Trivially $f_k(n)\leq F_k(n)$.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.exactly_le_atLeast (k n : ℕ) :
    maxLinesExactly k n ≤ maxLinesAtLeast k n := by
  sorry

/--
$f_2(n)=F_2(n)=\binom{n}{2}$.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.k_two (n : ℕ) :
    maxLinesExactly 2 n = n.choose 2 ∧ maxLinesAtLeast 2 n = n.choose 2 := by
  sorry

/--
The problem with $k=3$ is the classical 'Orchard problem' of Sylvester. Burr, Grünbaum, and Sloane
[BGS74] have proved that
$$f_3(n)=\frac{n^2}{6}-O(n)$$
and
$$F_3(n)=\frac{n^2}{6}-O(n).$$

This is the statement for $f_3$.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.burr_grunbaum_sloane_exactly :
    (fun n : ℕ => (maxLinesExactly 3 n : ℝ) - (n : ℝ) ^ 2 / 6) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  sorry

/--
The problem with $k=3$ is the classical 'Orchard problem' of Sylvester. Burr, Grünbaum, and Sloane
[BGS74] have proved that
$$f_3(n)=\frac{n^2}{6}-O(n)$$
and
$$F_3(n)=\frac{n^2}{6}-O(n).$$

This is the statement for $F_3$.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.burr_grunbaum_sloane_atLeast :
    (fun n : ℕ => (maxLinesAtLeast 3 n : ℝ) - (n : ℝ) ^ 2 / 6) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  sorry

/--
There is a trivial upper bound of $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.upper_bound (k n : ℕ) (hk : 2 ≤ k) :
    (maxLinesAtLeast k n : ℝ) ≤ (n.choose 2 : ℝ) / (k.choose 2 : ℝ) := by
  sorry

/--
There is a trivial upper bound of $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$, and hence
$$\lim F_k(n)/n^2 \leq \frac{1}{k(k-1)}.$$
See also [101](https://www.erdosproblems.com/101).

Here the limit is assumed to exist and is called `L`.
-/
@[category research solved, AMS 52]
theorem erdos_669.variants.limit_le (k : ℕ) (hk : 2 ≤ k) (L : ℝ)
    (hL : Tendsto (fun n : ℕ => (maxLinesAtLeast k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 L)) :
    L ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  sorry

end Erdos669
