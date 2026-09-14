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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Encoded geometric decision problems

Sources:
- Garey and Johnson, *Computers and Intractability* (1979), ND13 (p. 209)
  and ND23 (p. 212), including the rectilinear and exact Euclidean variants.
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Megiddo and Tamir, *On the complexity of locating linear facilities in the
  plane*, Operations Research Letters 1 (1982), 194–197.
  https://doi.org/10.1016/0167-6377(82)90039-6
- Clark, Colbourn, and Johnson, *Unit disk graphs*, Discrete Mathematics 86
  (1990), 165–177, §1 and §§4–5.
  https://doi.org/10.1016/0012-365X(90)90358-O

Coordinates and bounds use the existing binary encodings. Input point lists
must be duplicate-free. Exact Euclidean lengths are real square roots, not
rounded distances or sums of squared lengths. Steiner vertices range over
all finite sets of integer points. Covering lines have arbitrary real
coefficients. No artificial witness bound is imposed on either problem.

Unit-disk inputs provide rational centers and a positive rational proximity
threshold, equal to the disk diameter. Tangency counts as adjacency. Only the
two unit-disk predicates have executable exhaustive decision instances here.
-/

@[expose] public section

namespace Computability.GeometricProblems

/-- Binary-encoded rational coordinates. -/
abbrev Point := ℚ × ℚ

/-- The integer-coordinate input convention of ND13 and ND23. -/
abbrev IntegerPoint := ℤ × ℤ

/-- A coordinate pair in the actual Euclidean plane, not the product sup metric. -/
def toEuclidean (p : Point) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

/-- Exact rational squared Euclidean distance. -/
def squaredDistance (p q : Point) : ℚ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

theorem squaredDistance_comm (p q : Point) :
    squaredDistance p q = squaredDistance q p := by
  unfold squaredDistance
  ring

theorem squaredDistance_nonneg (p q : Point) : 0 ≤ squaredDistance p q :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[simp]
theorem squaredDistance_self (p : Point) : squaredDistance p p = 0 := by
  simp [squaredDistance]

/-- The coordinate formula agrees with Mathlib's Euclidean metric. -/
theorem dist_toEuclidean (p q : Point) :
    dist (toEuclidean p) (toEuclidean q) = Real.sqrt (squaredDistance p q : ℝ) := by
  rw [EuclideanSpace.dist_eq]
  simp [toEuclidean, squaredDistance, Fin.sum_univ_two, Real.dist_eq,
    sq_abs, Rat.cast_add, Rat.cast_sub, Rat.cast_pow]

/-- Squaring preserves a nonnegative proximity threshold, including tangency. -/
theorem dist_le_iff (p q : Point) {d : ℚ} (hd : 0 ≤ d) :
    dist (toEuclidean p) (toEuclidean q) ≤ (d : ℝ) ↔
      squaredDistance p q ≤ d ^ 2 := by
  rw [dist_toEuclidean, Real.sqrt_le_left (by exact_mod_cast hd)]
  exact_mod_cast (Iff.rfl : squaredDistance p q ≤ d ^ 2 ↔ _)

/-- An integer point viewed as a rational point. -/
def rationalPoint (p : IntegerPoint) : Point := (p.1, p.2)

/-- Exact Euclidean distance on integer-coordinate inputs. -/
noncomputable def euclideanLength (p q : IntegerPoint) : ℝ :=
  dist (toEuclidean (rationalPoint p)) (toEuclidean (rationalPoint q))

/-- Cyclic successor, also well-typed on the empty vertex type. -/
def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A cyclic tour pays for its return leg; two-point tours pay twice. -/
noncomputable def tourLength (points : List IntegerPoint)
    (order : Equiv.Perm (Fin points.length)) : ℝ :=
  ∑ i, euclideanLength points[order i] points[order (next i)]

/-- ND23's exact, non-discretized Euclidean variant, with a positive integer budget.
Empty and singleton tours have length zero. -/
def EuclideanTravelingSalesman (input : List IntegerPoint × ℕ) : Prop :=
  input.1.Nodup ∧ 0 < input.2 ∧
    ∃ order : Equiv.Perm (Fin input.1.length), tourLength input.1 order ≤ input.2

/-- The rectilinear (Manhattan) length used in ND13's metric variant. -/
def rectilinearLength (p q : IntegerPoint) : ℕ :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

theorem rectilinearLength_comm (p q : IntegerPoint) :
    rectilinearLength p q = rectilinearLength q p := by
  have h (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
    rw [← neg_sub a b, Int.natAbs_neg]
  simp only [rectilinearLength, h]

/-- The weight of an unordered edge; reversal does not double the contribution. -/
def rectilinearEdgeLength {s : Finset IntegerPoint} : Sym2 s → ℕ :=
  Sym2.lift ⟨fun p q ↦ rectilinearLength p.val q.val,
    fun p q ↦ rectilinearLength_comm p.val q.val⟩

/-- Total edge length of an actual finite Mathlib graph. -/
noncomputable def rectilinearTreeLength {s : Finset IntegerPoint}
    (G : SimpleGraph s) : ℕ := by
  classical
  exact ∑ e ∈ G.edgeFinset, rectilinearEdgeLength e

/-- The edge sum is independent of the choice of finite edge enumeration. -/
theorem rectilinearTreeLength_eq {s : Finset IntegerPoint} (G : SimpleGraph s)
    [Fintype G.edgeSet] :
    rectilinearTreeLength G = ∑ e ∈ G.edgeFinset, rectilinearEdgeLength e := by
  classical
  unfold rectilinearTreeLength
  congr 2
  exact Subsingleton.elim _ _

/-- ND13's rectilinear variant: a finite integer-point tree containing all input
terminals, within a positive integer budget. Steiner points are not input-restricted.
The witness set includes the terminals, equivalently it is the source's union P ∪ Q. -/
def RectilinearSteinerTree (input : List IntegerPoint × ℕ) : Prop :=
  input.1.Nodup ∧ 0 < input.2 ∧
    ∃ s : Finset IntegerPoint, (∀ p ∈ input.1, p ∈ s) ∧
      ∃ G : SimpleGraph s, G.IsTree ∧ rectilinearTreeLength G ≤ input.2

/-- A genuine affine line ax + by = c; the zero normal is excluded.
Coefficient form describes incidence directly without choosing a base point or direction. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  normal_ne_zero : a ≠ 0 ∨ b ≠ 0

/-- Incidence of an encoded rational point with an arbitrary real affine line. -/
def Line.Contains (l : Line) (p : Point) : Prop :=
  l.a * (p.1 : ℝ) + l.b * (p.2 : ℝ) = l.c

/-- A vertical line, also available to pad a covering family with unused lines. -/
def Line.vertical (x : ℝ) : Line := ⟨1, 0, x, Or.inl one_ne_zero⟩

/-- A horizontal line. -/
def Line.horizontal (y : ℝ) : Line := ⟨0, 1, y, Or.inr one_ne_zero⟩

/-- A nonzero normal prevents a purported line from covering the whole plane. -/
theorem Line.not_contains_all (l : Line) : ¬ ∀ p : Point, l.Contains p := by
  intro h
  have h0 := h (0, 0)
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  norm_num [Line.Contains] at h0 h1 h2
  rcases l.normal_ne_zero with ha | hb
  · exact ha (h1.trans h0.symm)
  · exact hb (h2.trans h0.symm)

/-- Cover the input points by at most the input number of straight lines.
A family of K lines may repeat or contain unused lines. K = 0 covers only the empty set. -/
def LineCover (input : List Point × ℕ) : Prop :=
  input.1.Nodup ∧ ∃ lines : Fin input.2 → Line,
    ∀ p ∈ input.1, ∃ i, (lines i).Contains p

@[simp]
theorem lineCover_zero_iff (points : List Point) : LineCover (points, 0) ↔ points = [] := by
  cases points with
  | nil => simp [LineCover]
  | cons p ps =>
    constructor
    · rintro ⟨_, lines, h⟩
      obtain ⟨i, _⟩ := h p (List.mem_cons_self ..)
      exact Fin.elim0 i
    · intro h
      cases h

/-- Rational centers, rational proximity threshold (disk diameter), and size bound. -/
abbrev UnitDiskInput := List Point × (ℚ × ℕ)

/-- The actual finite unit-disk graph, with a closed proximity threshold. -/
def unitDiskGraph (points : List Point) (d : ℚ) : SimpleGraph (Fin points.length) where
  Adj i j := i ≠ j ∧ squaredDistance points[i] points[j] ≤ d ^ 2
  symm := ⟨fun i j h ↦ ⟨h.1.symm,
    by simpa only [squaredDistance_comm] using h.2⟩⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

instance (points : List Point) (d : ℚ) : DecidableRel (unitDiskGraph points d).Adj := by
  unfold unitDiskGraph
  infer_instance

/-- A geometric independent set of at least K vertices. -/
def UnitDiskIndependentSet (input : UnitDiskInput) : Prop :=
  input.1.Nodup ∧ 0 < input.2.1 ∧
    ∃ s : Finset (Fin input.1.length), input.2.2 ≤ s.card ∧
      (unitDiskGraph input.1 input.2.1).IsIndepSet s

/-- At most K input centers cover every input center at the given proximity threshold.
Chosen centers cover themselves; centers outside the input are not permitted. -/
def UnitDiskDominatingSet (input : UnitDiskInput) : Prop :=
  input.1.Nodup ∧ 0 < input.2.1 ∧
    ∃ s : Finset (Fin input.1.length), s.card ≤ input.2.2 ∧
      ∀ i : Fin input.1.length, ∃ j ∈ s,
        squaredDistance input.1[i] input.1[j] ≤ input.2.1 ^ 2

instance (input : UnitDiskInput) : Decidable (UnitDiskIndependentSet input) := by
  unfold UnitDiskIndependentSet
  infer_instance

instance (input : UnitDiskInput) : Decidable (UnitDiskDominatingSet input) := by
  unfold UnitDiskDominatingSet
  infer_instance

/-- The metric predicate is precisely graph domination, including self-coverage. -/
theorem dominating_iff (points : List Point) (d : ℚ) (s : Finset (Fin points.length)) :
    (∀ i : Fin points.length, ∃ j ∈ s, squaredDistance points[i] points[j] ≤ d ^ 2) ↔
      ∀ i, i ∈ s ∨ ∃ j ∈ s, (unitDiskGraph points d).Adj i j := by
  constructor
  · intro h i
    obtain ⟨j, hj, hij⟩ := h i
    by_cases heq : i = j
    · exact Or.inl (heq ▸ hj)
    · exact Or.inr ⟨j, hj, heq, hij⟩
  · intro h i
    rcases h i with hi | ⟨j, hj, _, hij⟩
    · exact ⟨i, hi, by simpa using sq_nonneg d⟩
    · exact ⟨j, hj, hij⟩

end Computability.GeometricProblems
