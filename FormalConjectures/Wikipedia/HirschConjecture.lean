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
# The Hirsch conjecture and the polynomial Hirsch conjecture

The **Hirsch conjecture** (1957) asserted that the edge graph of a $d$-dimensional polytope with
$n$ facets has diameter at most $n - d$. Santos [San12] disproved it with a $43$-dimensional
polytope with $86$ facets. The conjecture is equivalent to its restriction to simple polytopes,
because pushing the facets of a polytope into general position gives a simple polytope with the
same dimension and number of facets whose diameter is at least as large.

The **polynomial Hirsch conjecture** asked for a weaker bound: the diameter is at most a fixed
polynomial in $n$. The best general upper bound before 2026 was quasi-polynomial
(Kalai–Kleitman [KK92], improved by Todd and Sukegawa). The conjecture matters for the simplex
method, since any edge-following pivot rule needs at least as many steps as the distance between
its start and the optimum. OpenAI [OAI26] disproved it: there are bounded simple rational polytopes
with $n$ facets and dimension $n^{o(1)}$ whose edge diameter eventually exceeds every power of $n$.

The setting below follows the Lean development of [OAI26]: a polytope is a nonempty compact set
cut out by finitely many rational inequalities, faces are convex extreme subsets, and two vertices
are adjacent in the edge graph when some face of dimension at most one contains both.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hirsch_conjecture)
- [San12] Santos, F., *A counterexample to the Hirsch conjecture*, Ann. of Math. (2) **176**
  (2012), 383–412, [arXiv:1006.2814](https://arxiv.org/abs/1006.2814).
- [KK92] Kalai, G. and Kleitman, D. J., *A quasi-polynomial bound for the diameter of graphs of
  polyhedra*, Bull. Amer. Math. Soc. **26** (1992), 315–316.
- [OAI26] OpenAI, *Superpolynomial graph diameter of simple polytopes*, OpenAI Math Release
  preprint, November 24, 2026.
  [paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026/paper.pdf)
-/

@[expose] public section

open Set Module

namespace HirschConjecture

section Faces

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- A face of `body` is a convex subset that is extreme in `body`. -/
structure IsFace (body face : Set V) : Prop where
  convex : Convex ℝ face
  extreme : IsExtreme ℝ body face

/-- The dimension of a set: the dimension of its affine span. -/
noncomputable def dim (s : Set V) : ℕ := finrank ℝ (vectorSpan ℝ s)

/-- The facets of `body`: nonempty faces of dimension one less than `body`. -/
def facets (body : Set V) : Set (Set V) :=
  {face | IsFace body face ∧ face.Nonempty ∧ dim face + 1 = dim body}

/-- `body` is simple when each vertex lies on exactly `dim body` facets. -/
def IsSimple (body : Set V) : Prop :=
  ∀ x ∈ body.extremePoints ℝ, {face ∈ facets body | x ∈ face}.ncard = dim body

/-- The edge graph of `body`: two distinct vertices are adjacent when a face of dimension at
most one contains both. -/
def edgeGraph (body : Set V) : SimpleGraph (body.extremePoints ℝ) where
  Adj x y := x ≠ y ∧ ∃ face, IsFace body face ∧ dim face ≤ 1 ∧ x.1 ∈ face ∧ y.1 ∈ face
  symm := ⟨by rintro _ _ ⟨hne, face, hf, hd, hx, hy⟩; exact ⟨hne.symm, face, hf, hd, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Faces

/-- A bounded rational polytope: a nonempty compact set `{x | ∀ i, b i ≤ a i x}` cut out by
finitely many inequalities with rational coefficients in some basis. -/
structure RationalPolytope where
  /-- The ambient space. -/
  V : Type
  [normed : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finiteDim : FiniteDimensional ℝ V]
  /-- Coordinates of a basis of `V`. -/
  ι : Type
  /-- The basis in which the inequalities are rational. -/
  basis : Basis ι ℝ V
  /-- The index type of the inequalities. -/
  Row : Type
  [finiteRow : Finite Row]
  /-- The linear part of each inequality. -/
  a : Row → V →ₗ[ℝ] ℝ
  /-- The right-hand side of each inequality. -/
  b : Row → ℝ
  rational_a : ∀ i j, ∃ q : ℚ, a i (basis j) = q
  rational_b : ∀ i, ∃ q : ℚ, b i = q
  compact : IsCompact {x | ∀ i, b i ≤ a i x}
  nonempty : {x | ∀ i, b i ≤ a i x}.Nonempty

attribute [instance] RationalPolytope.normed RationalPolytope.space RationalPolytope.finiteDim
  RationalPolytope.finiteRow

namespace RationalPolytope

variable (P : RationalPolytope)

/-- The point set of `P`. -/
def body : Set P.V := {x | ∀ i, P.b i ≤ P.a i x}

/-- The dimension of `P`. -/
noncomputable def dimension : ℕ := dim P.body

/-- The number of facets of `P`. -/
noncomputable def facetCount : ℕ := (facets P.body).ncard

end RationalPolytope

open RationalPolytope

/--
**Hirsch conjecture** (stated for simple polytopes, which is equivalent). The edge graph of a
simple polytope of dimension $d$ with $n$ facets has diameter at most $n - d$. This is false
[San12].
-/
@[category research solved, AMS 52 90]
theorem hirsch_conjecture :
    ¬ ∀ P : RationalPolytope, IsSimple P.body →
      ∀ x y : P.body.extremePoints ℝ,
        (edgeGraph P.body).dist x y ≤ P.facetCount - P.dimension := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
**Polynomial Hirsch conjecture.** There is a polynomial bound $C (n + 1)^k$ on the edge distance
between any two vertices of a simple polytope with $n$ facets. This is false [OAI26]. The edge
graph of a polytope is always connected (Balinski), so the connectivity hypothesis, which the
linked Lean statement also carries, costs nothing.
-/
@[category research solved, AMS 52 90,
  formal_proof using lean4 at "https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Main.lean#L106-L108"]
theorem polynomial_hirsch_conjecture :
    ¬ ∃ C k : ℕ, ∀ P : RationalPolytope, IsSimple P.body → (edgeGraph P.body).Connected →
      ∀ x y : P.body.extremePoints ℝ,
        (edgeGraph P.body).dist x y ≤ C * (P.facetCount + 1) ^ k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The quantitative form of [OAI26]: for every large $n$ there is a simple polytope with exactly $n$
facets, dimension $n^{o(1)}$ and edge diameter that eventually exceeds $n^c$ for every $c$.
-/
@[category research solved, AMS 52 90,
  formal_proof using lean4 at "https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Main.lean#L66-L70"]
theorem polynomial_hirsch_conjecture.variants.superpolynomial_diameter :
    ∃ P : ℕ → RationalPolytope,
      (∀ᶠ n in Filter.atTop, IsSimple (P n).body ∧ (edgeGraph (P n).body).Connected ∧
        (P n).facetCount = n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ((P n).dimension : ℝ) ≤ (n : ℝ) ^ ε) ∧
      ∀ c : ℝ, ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ c ≤ (edgeGraph (P n).body).diam := by
  sorry

end HirschConjecture
