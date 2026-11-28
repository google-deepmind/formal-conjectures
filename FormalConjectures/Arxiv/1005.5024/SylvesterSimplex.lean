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
# Sylvester's simplex conjecture in $\mathbb{R}^d$

For a compact convex body $K \subset \mathbb{R}^d$ with nonempty interior, let
$$M_{N,p}(K) = \frac{1}{\mathrm{Vol}_d(K)^{N+p}}
  \int_{K^N} \mathrm{Vol}_d(\mathrm{conv}(x_1,\dots,x_N))^p
  \,dx_1\cdots dx_N$$
be the normalized $p$-th moment of the volume of the convex hull of $N$ independent uniform
points of $K$. The Sylvester simplex conjecture states that, for every nondegenerate
$d$-simplex $T \subset \mathbb{R}^d$,
$$M_{d+1,1}(K) \le M_{d+1,1}(T),$$
with equality if and only if $K$ is a simplex.

Equivalently, if $P^{(d)}_K(n)$ is the probability that $n$ independent uniform points of $K$
are in convex position, then $P^{(d)}_K(d+2) = 1 - (d+2)M_{d+1,1}(K)$, so the conjecture says
that simplices minimize $P^{(d)}_K(d+2)$.

The planar case $d = 2$ is Blaschke's theorem. The conjecture is open for $d \ge 3$. The
ellipsoid counterpart, that ellipsoids minimize $M_{d+1,p}$, is Groemer's theorem in every
dimension.

*References:*
- [AB2014] G. Ambrus and K. J. Böröczky, *Stability results for the volume of random simplices*,
  *American Journal of Mathematics* **136**(4) (2014), 833–857.
  [DOI](https://doi.org/10.1353/ajm.2014.0030) ·
  [arXiv:1005.5024v2](https://arxiv.org/abs/1005.5024v2). Free-vertex case: §1.3, Conjecture 1
  (arXiv v2, p. 5); probability identity: §1.1 (arXiv v2, p. 2).
- [Blaschke1917] W. Blaschke, *Über affine Geometrie XI: Lösung des "Vierpunktproblems" von
  Sylvester aus der Theorie der geometrischen Wahrscheinlichkeiten*, *Berichte über die
  Verhandlungen der Sächsischen Akademie der Wissenschaften zu Leipzig, Mathematisch-Physische
  Klasse* **69** (1917), 436–453.
- [Pfiefer1989] R. E. Pfiefer, *The historical development of J. J. Sylvester's four point
  problem*, *Mathematics Magazine* **62**(5) (1989), 309–317.
  [DOI](https://doi.org/10.2307/2689482). Higher-dimensional attribution and the explicit
  three-dimensional conjecture: §4, p. 315.
- [Groemer1973] H. Groemer, *On some mean values associated with a randomly selected simplex in
  a convex set*, *Pacific Journal of Mathematics* **45**(2) (1973), 525–533.
  [DOI](https://doi.org/10.2140/pjm.1973.45.525). Ellipsoid minimum and equality case:
  unnumbered theorem and Corollaries 1–2, pp. 526–527.
- [MarckertMorin2026] J.-F. Marckert and L. Morin, *The Sylvester question in $\mathbb{R}^d$:
  convex sets with a flat floor*, *Electronic Journal of Probability* **31** (2026),
  article 114, 1–27. [DOI](https://doi.org/10.1214/26-EJP1563) ·
  [arXiv:2411.08456v2](https://arxiv.org/abs/2411.08456v2). Current open status: abstract and
  §1 around (1.1).
- [BuchtaReitzner2001] C. Buchta and M. Reitzner, *The convex hull of random points in a
  tetrahedron: Solution of Blaschke's problem and more general results*, *Journal für die reine
  und angewandte Mathematik* **536** (2001), 1–29.
  [DOI](https://doi.org/10.1515/crll.2001.050). Exact tetrahedron value
  $M_{4,1}(T^3) = 13/720 - \pi^2/15015$.
- [CCG1999] S. Campi, A. Colesanti, and P. Gronchi, *A note on Sylvester's problem for random
  polytopes in a convex body*, *Rendiconti dell'Istituto di Matematica dell'Università di
  Trieste* **31**(1–2) (1999), 79–94.
  [Repository copy](https://www.openstarts.units.it/items/ac389773-c662-480b-986a-f7e12e2a9494).
  Explicit simplex-only conjecture: summary, p. 79, and §1, p. 80.

The probability used here is the convex-position probability. Pfiefer and Campi–Colesanti–Gronchi
use the complementary probability that one point lies in the convex hull of the others.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace Arxiv.«1005.5024»

/-- A configuration of `n` points in `ℝ^d` is in **convex position** if every point is a vertex
of the convex hull of the configuration, i.e. no point lies in the convex hull of the others. -/
def InConvexPosition {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i : Fin n, x i ∉ convexHull ℝ (x '' {j : Fin n | j ≠ i})

/-- A **nondegenerate `d`-simplex** in `ℝ^d`: the convex hull of `d + 1` affinely independent
points. -/
def IsNondegenerateSimplex {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
    AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v)

/-- An **ellipsoid** in `ℝ^d`: an affine image of the closed unit ball. -/
def IsEllipsoid {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ φ : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d),
    K = φ '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The uniform probability measure on a convex body `K`: normalized Lebesgue measure restricted
to `K`. -/
noncomputable def uniformMeasure {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume K)⁻¹ • volume.restrict K

/-- The normalized `p`-th moment `M_{N,p}(K)` of the volume of the convex hull of `N`
independent uniform points of `K`:
$$M_{N,p}(K) = \frac{1}{\mathrm{Vol}_d(K)^{N+p}}
  \int_{K^N} \mathrm{Vol}_d(\mathrm{conv}(x_1,\dots,x_N))^p
  \,dx_1\cdots dx_N.$$
The value is in `ℝ≥0∞`; for a convex body it is finite. -/
noncomputable def meanSimplexVolume {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (N p : ℕ) : ℝ≥0∞ :=
  (volume K ^ (N + p))⁻¹ *
    ∫⁻ x : Fin N → EuclideanSpace ℝ (Fin d),
      volume (convexHull ℝ (Set.range x)) ^ p
        ∂(Measure.pi (fun _ : Fin N => volume.restrict K))

/-- The probability `P^{(d)}_K(N)` that `N` independent uniform points of `K` are in convex
position. -/
noncomputable def convexPositionProbability {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (N : ℕ) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin N => uniformMeasure K)) {x | InConvexPosition x}

/-- The normalized moment is invariant under affine equivalences. -/
@[category API, AMS 52]
theorem meanSimplexVolume_affine {d N p : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    meanSimplexVolume (φ '' K) N p = meanSimplexVolume K N p := by
  sorry

/-- All nondegenerate `d`-simplices have the same normalized moment. -/
@[category API, AMS 52]
theorem meanSimplexVolume_simplex_eq {d : ℕ}
    (S T : Set (EuclideanSpace ℝ (Fin d)))
    (hS : IsNondegenerateSimplex S) (hT : IsNondegenerateSimplex T) :
    meanSimplexVolume S (d + 1) 1 = meanSimplexVolume T (d + 1) 1 := by
  sorry

/-- **The $(d+2)$-point identity** [AB2014, §1.1]. For a convex body `K` in `ℝ^d`, the
probability that `d+2` uniform points of `K` are in convex position is
`1 - (d+2) M_{d+1,1}(K)`.

This identity is special to `d+2` points; it does not extend to more points. -/
@[category API, AMS 52 60]
theorem convexPositionProbability_eq_one_sub (d : ℕ) (hd : 2 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    convexPositionProbability K (d + 2) =
      1 - (d + 2 : ℝ≥0∞) * meanSimplexVolume K (d + 1) 1 := by
  sorry

/-- **Sylvester's simplex conjecture.** For every compact convex body $K \subset \mathbb{R}^d$
with nonempty interior and every nondegenerate $d$-simplex $T \subset \mathbb{R}^d$, the
normalized expected volume of a random simplex with $d+1$ vertices is at most the corresponding
value for $T$.

This is the free-vertex case of Conjecture 1 of [AB2014], at $p = 1$ and $n = d+1$. The
conjecture is open for $d \ge 3$; the case $d = 2$ is Blaschke's theorem. -/
@[category research open, AMS 52 60]
theorem sylvester_simplex_conjecture (d : ℕ) (hd : 3 ≤ d)
    (K T : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (hT : IsNondegenerateSimplex T) :
    meanSimplexVolume K (d + 1) 1 ≤ meanSimplexVolume T (d + 1) 1 := by
  sorry

/-- **Rigidity in Sylvester's simplex conjecture.** Equality holds if and only if `K` is a
nondegenerate `d`-simplex.

The converse direction, that every simplex attains equality, is affine invariance
(`meanSimplexVolume_simplex_eq`); the open content is the only-if direction. -/
@[category research open, AMS 52 60]
theorem sylvester_simplex_conjecture.eq_iff (d : ℕ) (hd : 3 ≤ d)
    (K T : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (hT : IsNondegenerateSimplex T) :
    meanSimplexVolume K (d + 1) 1 = meanSimplexVolume T (d + 1) 1 ↔
      IsNondegenerateSimplex K := by
  sorry

/-- **Sylvester's simplex conjecture, probability form.** For $d \ge 3$, the probability that
$d+2$ uniform points of a convex body $K \subset \mathbb{R}^d$ are in convex position is at least
the corresponding probability for a nondegenerate $d$-simplex.

This is equivalent to `sylvester_simplex_conjecture` by
`convexPositionProbability_eq_one_sub`. -/
@[category research open, AMS 52 60]
theorem sylvester_probability_conjecture (d : ℕ) (hd : 3 ≤ d)
    (K T : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (hT : IsNondegenerateSimplex T) :
    convexPositionProbability T (d + 2) ≤ convexPositionProbability K (d + 2) := by
  sorry

/-- **Blaschke's planar upper bound** [Blaschke1917]. For a convex body
$K \subset \mathbb{R}^2$, the normalized expected area of a random triangle in $K$ is at most
$1/12$, with equality if and only if $K$ is a triangle.

Equivalently, four uniform points of $K$ are in convex position with probability at least
$2/3$. -/
@[category research solved, AMS 52 60]
theorem blaschke_planar_upper (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    meanSimplexVolume K 3 1 ≤ ENNReal.ofReal (1 / 12) := by
  sorry

/-- Equality in Blaschke's planar upper bound holds exactly for triangles. -/
@[category research solved, AMS 52 60]
theorem blaschke_planar_upper.eq_iff (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    meanSimplexVolume K 3 1 = ENNReal.ofReal (1 / 12) ↔ IsNondegenerateSimplex K := by
  sorry

/-- **Blaschke's planar lower bound** [Blaschke1917]. For a convex body
$K \subset \mathbb{R}^2$, the normalized expected area of a random triangle in $K$ is at least
$\frac{35}{48\pi^2}$, with equality if and only if $K$ is an ellipse.

Equivalently, four uniform points of $K$ are in convex position with probability at most
$1 - \frac{35}{12\pi^2}$. -/
@[category research solved, AMS 52 60]
theorem blaschke_planar_lower (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    ENNReal.ofReal (35 / (48 * Real.pi ^ 2)) ≤ meanSimplexVolume K 3 1 := by
  sorry

/-- Equality in Blaschke's planar lower bound holds exactly for ellipses. -/
@[category research solved, AMS 52 60]
theorem blaschke_planar_lower.eq_iff (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    meanSimplexVolume K 3 1 = ENNReal.ofReal (35 / (48 * Real.pi ^ 2)) ↔ IsEllipsoid K := by
  sorry

/-- **Groemer's ellipsoid theorem** [Groemer1973]. For every $d \ge 2$ and every $p \ge 1$,
ellipsoids minimize the normalized $p$-th moment of the volume of a random simplex with $d+1$
vertices; equality holds if and only if `K` is an ellipsoid. -/
@[category research solved, AMS 52 60]
theorem groemer_ellipsoid_lower (d : ℕ) (hd : 2 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (p : ℕ) (hp : 1 ≤ p) :
    meanSimplexVolume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (d + 1) p ≤
      meanSimplexVolume K (d + 1) p := by
  sorry

/-- Equality in Groemer's ellipsoid theorem holds exactly for ellipsoids. -/
@[category research solved, AMS 52 60]
theorem groemer_ellipsoid_lower.eq_iff (d : ℕ) (hd : 2 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (p : ℕ) (hp : 1 ≤ p) :
    meanSimplexVolume K (d + 1) p =
        meanSimplexVolume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (d + 1) p ↔
      IsEllipsoid K := by
  sorry

/-- The exact normalized expected volume of a random tetrahedron in a tetrahedron
[BuchtaReitzner2001]: $M_{4,1}(T^3) = \frac{13}{720} - \frac{\pi^2}{15015}$.

This is an exact computation, not a proof of tetrahedron extremality. -/
@[category research solved, AMS 52 60]
theorem tetrahedron_mean_volume (T : Set (EuclideanSpace ℝ (Fin 3)))
    (hT : IsNondegenerateSimplex T) :
    meanSimplexVolume T 4 1 = ENNReal.ofReal (13 / 720 - Real.pi ^ 2 / 15015) := by
  sorry

/-- The exact normalized expected volume of a random tetrahedron in a ball in $\mathbb{R}^3$:
$M_{4,1}(B^3) = \frac{9}{715}$ (see [AB2014, Theorem 1]).

This is an exact computation, not a proof of ellipsoid extremality. -/
@[category research solved, AMS 52 60]
theorem ball_mean_volume_three :
    meanSimplexVolume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) 4 1 =
      ENNReal.ofReal (9 / 715) := by
  sorry

/-- The convex-position probability is at most one. -/
@[category test, AMS 52 60]
theorem convexPositionProbability_le_one (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (N : ℕ) :
    convexPositionProbability K N ≤ 1 := by
  sorry

/-- For at most `d + 1` points, affine independence holds almost surely, so the points are in
convex position almost surely. -/
@[category test, AMS 52]
theorem convexPositionProbability_eq_one_of_le (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty)
    (N : ℕ) (hN : N ≤ d + 1) :
    convexPositionProbability K N = 1 := by
  sorry

end Arxiv.«1005.5024»
