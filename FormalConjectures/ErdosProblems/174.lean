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
# Erdős Problem 174

*References:*
- [erdosproblems.com/174](https://www.erdosproblems.com/174)
- [EGMRSS73] Erdős, P. and Graham, R. L. and Montgomery, P. and Rothschild, B. L. and Spencer,
  J. and Straus, E. G., *Euclidean Ramsey Theorems I*. J. Comb. Th. A (1973), 341-363.
  [PDF](https://www.renyi.hu/~p_erdos/1973-08.pdf)
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99-108. [PDF](https://www.renyi.hu/~p_erdos/1975-25.pdf)
- [FrRo90] Frankl, P. and Rödl, V., *A partition property of simplices in Euclidean space*.
  J. Amer. Math. Soc. (1990), 1-7.
- [Kr92] Kříž, Igor, *All trapezoids are Ramsey*. Discrete Math. (1992), 59-62.
- [LRW12] Leader, Imre and Russell, Paul A. and Walters, Mark, *Transitive sets in Euclidean
  Ramsey theory*. J. Combin. Theory Ser. A (2012), 382-396.
  [arXiv:1012.1350](https://arxiv.org/abs/1012.1350)
-/

@[expose] public section

namespace Erdos174

/-- A finite set `A ⊆ ℝⁿ` is Ramsey if for every number `k ≥ 1` of colours there is a
dimension `d` such that every colouring of `ℝᵈ` with `k` colours has a monochromatic copy of
`A`. A copy of `A` is the image of a map `p : A → ℝᵈ` that preserves all distances. -/
def IsRamsey {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  A.Finite ∧ ∀ k : ℕ, 1 ≤ k → ∃ d : ℕ, ∀ c : EuclideanSpace ℝ (Fin d) → Fin k,
    ∃ p : A → EuclideanSpace ℝ (Fin d),
      Congruent (fun a : A ↦ (a : EuclideanSpace ℝ (Fin n))) p ∧ ∃ i, ∀ a, c (p a) = i

/-- A finite set `X ⊆ ℝᵐ` is transitive if its symmetry group acts transitively: any point of
`X` is mapped to any other point of `X` by an isometry of `ℝᵐ` that maps `X` onto itself
[LRW12]. -/
def IsTransitive {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  X.Finite ∧ ∀ x ∈ X, ∀ y ∈ X,
    ∃ g : EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m), g '' X = X ∧ g x = y

/-- A set `A ⊆ ℝⁿ` is subtransitive if it is congruent to a subset of a finite transitive set in
some `ℝᵐ`; the dimension `m` may be larger than `n` [LRW12]. -/
def IsSubtransitive {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (m : ℕ) (Y : Set (EuclideanSpace ℝ (Fin m))), IsTransitive Y ∧
    ∃ p : A → EuclideanSpace ℝ (Fin m),
      Congruent (fun a : A ↦ (a : EuclideanSpace ℝ (Fin n))) p ∧ ∀ a, p a ∈ Y

/-- A single point is a Ramsey set. -/
@[category test, AMS 5 52]
theorem isRamsey_singleton {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : IsRamsey {x} :=
  ⟨Set.finite_singleton x, fun _ _ ↦ ⟨0, fun c ↦
    ⟨fun _ ↦ 0, Congruent.of_subsingleton_index, c 0, fun _ ↦ rfl⟩⟩⟩

def erdos_174.answer (n : ℕ) : Set (Set (EuclideanSpace ℝ (Fin n))) := sorry

/--
A finite set $A\subset \mathbb{R}^n$ is called Ramsey if, for any $k\geq 1$, there exists some
$d=d(A,k)$ such that in any $k$-colouring of $\mathbb{R}^d$ there exists a monochromatic copy
of $A$. Characterise the Ramsey sets in $\mathbb{R}^n$.

A copy of $A$ is a set congruent to $A$, as in [EGMRSS73, p. 344].
-/
@[category research open, question value, AMS 5 52]
theorem erdos_174 (n : ℕ) :
    {A : Set (EuclideanSpace ℝ (Fin n)) | IsRamsey A} = erdos_174.answer n := by
  sorry

/--
Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus [EGMRSS73] proved that every Ramsey
set is 'spherical': it lies on the surface of some sphere.
-/
@[category research solved, AMS 5 52]
theorem erdos_174.variants.spherical {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : IsRamsey A) : EuclideanGeometry.Cospherical A := by
  sorry

/--
Graham has conjectured that every spherical set is Ramsey.
-/
@[category research open, AMS 5 52]
theorem erdos_174.variants.graham {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : A.Finite) (hs : EuclideanGeometry.Cospherical A) : IsRamsey A := by
  sorry

/--
Leader, Russell, and Walters [LRW12] have alternatively conjectured that a set is Ramsey if and
only if it is 'subtransitive': it can be embedded in some higher-dimensional set on which
rotations act transitively.

We use the definition of [LRW12]: a subset of a finite set whose symmetry group acts
transitively.
-/
@[category research open, AMS 5 52]
theorem erdos_174.variants.leader_russell_walters {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : A.Finite) :
    IsRamsey A ↔ IsSubtransitive A := by
  sorry

/--
Sets known to be Ramsey include vertices of $k$-dimensional rectangles [EGMRSS73].

This is the case of the vertices `{x | ∀ i, x i = 0 ∨ x i = a i}` of a rectangular
parallelepiped [EGMRSS73, Cor. 21]; some $a_i$ may be $0$ [EGMRSS73, Cor. 22].
-/
@[category research solved, AMS 5 52]
theorem erdos_174.variants.brick {n : ℕ} (a : Fin n → ℝ) :
    IsRamsey {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i = 0 ∨ x i = a i} := by
  sorry

/--
Sets known to be Ramsey include non-degenerate simplices [FrRo90].

A non-degenerate simplex is a set of affinely independent points.
-/
@[category research solved, AMS 5 52]
theorem erdos_174.variants.simplex {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : AffineIndependent ℝ (Subtype.val : A → EuclideanSpace ℝ (Fin n))) :
    IsRamsey A := by
  sorry

/--
Sets known to be Ramsey include trapezoids [Kr92].

We state it for isosceles trapezoids with vertices $(\pm s, 0)$ and $(\pm t, h)$, $h\neq 0$.
A trapezoid that is not isosceles is not spherical, so it is not Ramsey by [EGMRSS73].
-/
@[category research solved, AMS 5 52]
theorem erdos_174.variants.trapezoid (s t h : ℝ) (hh : h ≠ 0) :
    IsRamsey ({!₂[-s, 0], !₂[s, 0], !₂[-t, h], !₂[t, h]} :
      Set (EuclideanSpace ℝ (Fin 2))) := by
  sorry

end Erdos174
