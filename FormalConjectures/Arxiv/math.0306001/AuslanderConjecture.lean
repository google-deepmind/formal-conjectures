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

import FormalConjecturesUtil

/-!
# Auslander Conjecture in Homological Algebra
*Reference:*
We use the Artin-algebra formulation of the Auslander Conjecture following D.A. Jorgensen and L.M. Şega
[Nonvanishing cohomology and classes of Gorenstein rings](https://arxiv.org/abs/math/0306001),
published in
[Adv. Math. 188 (2004), 470-490](https://doi.org/10.1016/j.aim.2003.11.003).
The Auslander Conjecture was disproved in this article.

Remarks:

The counterexamples of Jorgensen and Şega are based on certain commutative finite-dimensional algebras introduced by V. Gasharov and I. Peeva
[Boundedness versus periodicity over commutative local rings, Trans. Amer. Math. Soc. 320 (1990), 569-580](https://doi.org/10.1090/S0002-9947-1990-0967311-0)

In a 1990 lecture note, D. Happel attributed to Maurice Auslander a more restrictive formulation of the conjecture,
concerning finite-dimensional algebras over algebraically closed fields:
[Homological conjectures in representation theory of finite-dimensional algebras](https://www.math.uni-bielefeld.de/~sek/dim2/happel2.pdf).
The work of Jorgensen and Şega disproves this more restrictive formulation as well.

According to Happel, Auslander observed that a finite-dimensional algebra $A$ over a field $k$ has finite little left finitistic dimension if
its enveloping algebra $A ⊗_k A^{\rm{op}}$ satisfies the Auslander Conjecture.
Thus, for finite-dimensional algebras, the study of the Auslander Conjecture can be motivated by the study of the Little Finitistic Dimension Conjecture.

The conjecture should not be confused with the Auslander Conjecture of Louis Auslander on affine crystallographic groups.
-/

open CategoryTheory.Abelian

namespace Arxiv.«math.0306001»

/-
## The Jorgensen-Şega counterexample

The proof below uses the smallest counterexample of the article: for a field $k$ and a nonzero
`α : k`, the commutative local `k`-algebra `B α = k[X₁, X₂, X₃, X₄]/Jα`, where `Jα` is generated
by the seven quadrics

  `α X₁X₃ + X₂X₃`, `X₁X₄ + X₂X₄`, `X₃²`, `X₄²`, `X₁²`, `X₂²`, `X₃X₄`.

It is the quotient `A α / (x₅)` of a Gorenstein algebra `A α` studied by Gasharov and Peeva.

The counterexample modules are `L`, the image of the map `(B α)² → (B α)²` given by the matrix
`!![x₁, x₃; x₄, x₂]`, and the family `T q = B α / (x₁ - x₂, x₁ - α ^ q * x₃, x₁ - x₄)`.

`AuslanderConjecture` below is proved outright. The refutation needs two cohomological facts,
`JorgensenSega.subsingleton_ext_of_lt` (the vanishing that makes `T q` an admissible test module)
and `JorgensenSega.not_subsingleton_ext_self` (the non-vanishing in the arbitrarily large degree
`q`), and both are read off the projective resolution `JorgensenSega.res`. Its exactness
[Lemma 2.2] is `JorgensenSega.ker_eq_range`, proved from an explicit eight-dimensional $k$-basis
 of $B_\alpha$ established in `JorgensenSega.exists_combo` and `JorgensenSega.combo_eq_zero`.

`JorgensenSega.ext_L_T_ne_zero` records [Corollary 3.3(2)] in the degrees the refutation uses: for
$i \ge q$ the cohomology is nonzero exactly in degree $q$. The corollary in the article is
stronger, asserting non-vanishing in the degrees $0$ and $q - 1$ as well; that part is not
needed here.
-/

namespace JorgensenSega

open MvPolynomial

universe u v

variable {k : Type u} [Field k]

/-- The seven quadrics generating the ideal $J_\alpha$ of $k[X_1, X_2, X_3, X_4]$, indexed so
that `X 0, X 1, X 2, X 3` are $X_1, X_2, X_3, X_4$. -/
def relations (α : k) : Set (MvPolynomial (Fin 4) k) :=
  {C α * X 0 * X 2 + X 1 * X 2, X 0 * X 3 + X 1 * X 3, X 2 ^ 2, X 3 ^ 2, X 0 ^ 2, X 1 ^ 2,
    X 2 * X 3}

/-- The algebra $B_\alpha = k[X_1, X_2, X_3, X_4]/J_\alpha$ of [Section 2]. -/
abbrev B (α : k) : Type u := MvPolynomial (Fin 4) k ⧸ Ideal.span (relations α)

noncomputable section

/-- The image $x_{i+1}$ of the variable $X_{i+1}$ in $B_\alpha$. -/
def gen (α : k) (i : Fin 4) : B α := Ideal.Quotient.mk _ (X i)

/-- The image of a defining relation vanishes in $B_\alpha$. -/
@[category API, AMS 13 16]
theorem mk_eq_zero_of_mem_relations (α : k) {p : MvPolynomial (Fin 4) k} (hp : p ∈ relations α) :
    (Ideal.Quotient.mk (Ideal.span (relations α)) p : B α) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hp)

@[category API, AMS 13 16, simp]
theorem mk_C (α a : k) :
    (Ideal.Quotient.mk (Ideal.span (relations α)) (C a) : B α) = algebraMap k (B α) a := rfl

/-- Every generator $x_{i+1}$ of $B_\alpha$ squares to zero, since all four squares
$X_1^2, X_2^2, X_3^2, X_4^2$ occur among the defining relations. -/
@[category API, AMS 13 16]
theorem gen_sq (α : k) (i : Fin 4) : gen α i ^ 2 = 0 := by
  have h : (X i : MvPolynomial (Fin 4) k) ^ 2 ∈ Ideal.span (relations α) :=
    Ideal.subset_span (by fin_cases i <;> simp [relations])
  rw [gen, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact h

/-- The defining relation $x_3x_4 = 0$. -/
@[category API, AMS 13 16]
theorem rel_x₃x₄ (α : k) : gen α 2 * gen α 3 = 0 := by
  have h := mk_eq_zero_of_mem_relations α (p := X 2 * X 3) (by simp [relations])
  rw [map_mul] at h
  exact h

/-- The defining relation $x_1x_4 + x_2x_4 = 0$. -/
@[category API, AMS 13 16]
theorem rel_x₁x₄ (α : k) : gen α 0 * gen α 3 + gen α 1 * gen α 3 = 0 := by
  have h := mk_eq_zero_of_mem_relations α (p := X 0 * X 3 + X 1 * X 3) (by simp [relations])
  rw [map_add, map_mul, map_mul] at h
  exact h

/-- The defining relation $\alpha x_1x_3 + x_2x_3 = 0$. -/
@[category API, AMS 13 16]
theorem rel_x₁x₃ (α : k) :
    algebraMap k (B α) α * gen α 0 * gen α 2 + gen α 1 * gen α 2 = 0 := by
  have h := mk_eq_zero_of_mem_relations α (p := C α * X 0 * X 2 + X 1 * X 2) (by simp [relations])
  rw [map_add, map_mul, map_mul, map_mul, mk_C] at h
  exact h

/- The eight monomials $1$; $x_1, x_2, x_3, x_4$; $x_1x_2, x_1x_3, x_1x_4$ form a $k$-basis of
$B_\alpha$, which is the Hilbert series $1 + 4t + 3t^2$ of [Section 2] made explicit. Both halves
of that statement are needed for [Lemma 2.2]: spanning, to write a general element of $B_\alpha$
down, and linear independence, to read coefficients off an equation. Independence is obtained by
mapping $B_\alpha$ onto an explicit eight dimensional model algebra. -/

/-- The $k$-bilinear form $k^4 \times k^4 \to k^3$ recording the product of two degree one
elements of $B_\alpha$ in the basis $x_1x_2, x_1x_3, x_1x_4$: the defining relations give
$x_2x_3 = -\alpha x_1x_3$ and $x_2x_4 = -x_1x_4$, while the four squares and $x_3x_4$ vanish. -/
def modelMul (α : k) (v w : Fin 4 → k) : Fin 3 → k :=
  ![v 0 * w 1 + v 1 * w 0,
    v 0 * w 2 + v 2 * w 0 - α * (v 1 * w 2 + v 2 * w 1),
    v 0 * w 3 + v 3 * w 0 - (v 1 * w 3 + v 3 * w 1)]

@[category API, AMS 13 16, simp]
theorem modelMul_zero (α : k) (v w : Fin 4 → k) :
    modelMul α v w 0 = v 0 * w 1 + v 1 * w 0 := rfl

@[category API, AMS 13 16, simp]
theorem modelMul_one (α : k) (v w : Fin 4 → k) :
    modelMul α v w 1 = v 0 * w 2 + v 2 * w 0 - α * (v 1 * w 2 + v 2 * w 1) := rfl

@[category API, AMS 13 16, simp]
theorem modelMul_two (α : k) (v w : Fin 4 → k) :
    modelMul α v w 2 = v 0 * w 3 + v 3 * w 0 - (v 1 * w 3 + v 3 * w 1) := rfl

/-- The model algebra $E_\alpha = k \oplus k^4 \oplus k^3$ for $B_\alpha$. The three summands sit
in degrees $0, 1, 2$, multiplication of two degree one elements is `JorgensenSega.modelMul`, and
every product of three elements of positive degree vanishes. -/
@[ext]
structure Model (α : k) where
  /-- The component in degree $0$. -/
  const : k
  /-- The component in degree $1$, in the basis $x_1, x_2, x_3, x_4$. -/
  lin : Fin 4 → k
  /-- The component in degree $2$, in the basis $x_1x_2, x_1x_3, x_1x_4$. -/
  quad : Fin 3 → k

namespace Model

variable {α : k}

instance : Zero (Model α) := ⟨⟨0, 0, 0⟩⟩

instance : One (Model α) := ⟨⟨1, 0, 0⟩⟩

instance : Add (Model α) :=
  ⟨fun x y => ⟨x.const + y.const, x.lin + y.lin, x.quad + y.quad⟩⟩

instance : Neg (Model α) := ⟨fun x => ⟨-x.const, -x.lin, -x.quad⟩⟩

instance : Mul (Model α) :=
  ⟨fun x y => ⟨x.const * y.const, x.const • y.lin + y.const • x.lin,
    x.const • y.quad + y.const • x.quad + modelMul α x.lin y.lin⟩⟩

@[category API, AMS 13 16, simp]
theorem zero_const : (0 : Model α).const = 0 := rfl

@[category API, AMS 13 16, simp]
theorem zero_lin : (0 : Model α).lin = 0 := rfl

@[category API, AMS 13 16, simp]
theorem zero_quad : (0 : Model α).quad = 0 := rfl

@[category API, AMS 13 16, simp]
theorem one_const : (1 : Model α).const = 1 := rfl

@[category API, AMS 13 16, simp]
theorem one_lin : (1 : Model α).lin = 0 := rfl

@[category API, AMS 13 16, simp]
theorem one_quad : (1 : Model α).quad = 0 := rfl

@[category API, AMS 13 16, simp]
theorem add_const (x y : Model α) : (x + y).const = x.const + y.const := rfl

@[category API, AMS 13 16, simp]
theorem add_lin (x y : Model α) : (x + y).lin = x.lin + y.lin := rfl

@[category API, AMS 13 16, simp]
theorem add_quad (x y : Model α) : (x + y).quad = x.quad + y.quad := rfl

@[category API, AMS 13 16, simp]
theorem neg_const (x : Model α) : (-x).const = -x.const := rfl

@[category API, AMS 13 16, simp]
theorem neg_lin (x : Model α) : (-x).lin = -x.lin := rfl

@[category API, AMS 13 16, simp]
theorem neg_quad (x : Model α) : (-x).quad = -x.quad := rfl

@[category API, AMS 13 16, simp]
theorem mul_const (x y : Model α) : (x * y).const = x.const * y.const := rfl

@[category API, AMS 13 16, simp]
theorem mul_lin (x y : Model α) : (x * y).lin = x.const • y.lin + y.const • x.lin := rfl

@[category API, AMS 13 16, simp]
theorem mul_quad (x y : Model α) :
    (x * y).quad = x.const • y.quad + y.const • x.quad + modelMul α x.lin y.lin := rfl

omit [Field k] in
/-- Two elements of the model algebra are equal as soon as all eight coordinates agree. Every
later computation in $E_\alpha$ goes through this lemma, so that `fin_cases` is needed here
only. -/
@[category API, AMS 13 16]
theorem ext' {x y : Model α} (hc : x.const = y.const) (h0 : x.lin 0 = y.lin 0)
    (h1 : x.lin 1 = y.lin 1) (h2 : x.lin 2 = y.lin 2) (h3 : x.lin 3 = y.lin 3)
    (q0 : x.quad 0 = y.quad 0) (q1 : x.quad 1 = y.quad 1) (q2 : x.quad 2 = y.quad 2) :
    x = y := by
  refine Model.ext hc (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i <;> assumption
  · fin_cases i <;> assumption

instance : CommRing (Model α) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub a b := a + -b
  add_assoc a b c := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  zero_add a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  add_zero a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  add_comm a b := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  neg_add_cancel a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  left_distrib a b c := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  right_distrib a b c := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  zero_mul a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_zero a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_assoc a b c := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  one_mul a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_one a := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_comm a b := by refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

end Model

/-- The structural map $k \to E_\alpha$. -/
def modelC (α : k) : k →+* Model α where
  toFun c := ⟨c, 0, 0⟩
  map_one' := rfl
  map_mul' c c' := by refine Model.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  map_zero' := rfl
  map_add' c c' := by refine Model.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

instance (α : k) : Algebra k (Model α) := RingHom.toAlgebra (modelC α)

@[category API, AMS 13 16, simp]
theorem Model.algebraMap_const (α c : k) : (algebraMap k (Model α) c).const = c := rfl

@[category API, AMS 13 16, simp]
theorem Model.algebraMap_lin (α c : k) : (algebraMap k (Model α) c).lin = 0 := rfl

@[category API, AMS 13 16, simp]
theorem Model.algebraMap_quad (α c : k) : (algebraMap k (Model α) c).quad = 0 := rfl

/-- The images in $E_\alpha$ of the four generators $x_1, x_2, x_3, x_4$. -/
def modelVals (α : k) : Fin 4 → Model α :=
  ![⟨0, ![1, 0, 0, 0], 0⟩, ⟨0, ![0, 1, 0, 0], 0⟩, ⟨0, ![0, 0, 1, 0], 0⟩, ⟨0, ![0, 0, 0, 1], 0⟩]

/-- The $k$-algebra map $B_\alpha \to E_\alpha$ sending $x_{i+1}$ to the $i$-th degree one basis
vector. The seven defining relations are exactly the seven identities built into
`JorgensenSega.modelMul`, so they are killed. -/
def toModel (α : k) : B α →ₐ[k] Model α :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (modelVals α)) <| by
    intro a ha
    have hle : Ideal.span (relations α) ≤
        RingHom.ker (MvPolynomial.aeval (modelVals α) :
          MvPolynomial (Fin 4) k →ₐ[k] Model α).toRingHom := by
      rw [Ideal.span_le]
      rintro r hr
      simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [SetLike.mem_coe, RingHom.mem_ker]
          refine Model.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [modelVals, sq]
    exact hle ha

@[category API, AMS 13 16, simp]
theorem toModel_mk (α : k) (p : MvPolynomial (Fin 4) k) :
    toModel α (Ideal.Quotient.mk (Ideal.span (relations α)) p)
      = MvPolynomial.aeval (modelVals α) p := rfl

@[category API, AMS 13 16, simp]
theorem toModel_gen (α : k) (i : Fin 4) : toModel α (gen α i) = modelVals α i := by
  rw [gen, toModel_mk, MvPolynomial.aeval_X]

/-- The relation $x_{i+1}^2 = 0$ in product rather than power form. -/
@[category API, AMS 13 16]
theorem gen_mul_self (α : k) (i : Fin 4) : gen α i * gen α i = 0 := by
  rw [← sq]
  exact gen_sq α i

/-- The relation $x_2x_3 = -\alpha x_1x_3$. -/
@[category API, AMS 13 16]
theorem gen₂_mul_gen₃ (α : k) :
    gen α 1 * gen α 2 = -(algebraMap k (B α) α * (gen α 0 * gen α 2)) := by
  linear_combination rel_x₁x₃ α

/-- The relation $x_2x_4 = -x_1x_4$. -/
@[category API, AMS 13 16]
theorem gen₂_mul_gen₄ (α : k) : gen α 1 * gen α 3 = -(gen α 0 * gen α 3) := by
  linear_combination rel_x₁x₄ α

/-- The $k$-linear combination of the eight monomials $1$; $x_1, x_2, x_3, x_4$;
$x_1x_2, x_1x_3, x_1x_4$ with the given coefficients. -/
def combo (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) : B α :=
  algebraMap k (B α) c₀
    + algebraMap k (B α) c₁ * gen α 0
    + algebraMap k (B α) c₂ * gen α 1
    + algebraMap k (B α) c₃ * gen α 2
    + algebraMap k (B α) c₄ * gen α 3
    + algebraMap k (B α) c₅ * (gen α 0 * gen α 1)
    + algebraMap k (B α) c₆ * (gen α 0 * gen α 2)
    + algebraMap k (B α) c₇ * (gen α 0 * gen α 3)

/-- Multiplying a combination of the eight monomials by $x_1$ gives another one. -/
@[category API, AMS 13 16]
theorem combo_mul_gen₁ (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) :
    combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ * gen α 0 = combo α 0 c₀ 0 0 0 c₂ c₃ c₄ := by
  simp only [combo, map_zero]
  linear_combination
    (algebraMap k (B α) c₁ + algebraMap k (B α) c₅ * gen α 1
      + algebraMap k (B α) c₆ * gen α 2 + algebraMap k (B α) c₇ * gen α 3) *
      gen_mul_self α 0

/-- Multiplying a combination of the eight monomials by $x_2$ gives another one. -/
@[category API, AMS 13 16]
theorem combo_mul_gen₂ (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) :
    combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ * gen α 1
      = combo α 0 0 c₀ 0 0 c₁ (-(α * c₃)) (-c₄) := by
  simp only [combo, map_zero, map_neg, map_mul]
  linear_combination
    (algebraMap k (B α) c₂ + algebraMap k (B α) c₅ * gen α 0) * gen_mul_self α 1
      + (algebraMap k (B α) c₃ + algebraMap k (B α) c₆ * gen α 0) * gen₂_mul_gen₃ α
      + (algebraMap k (B α) c₄ + algebraMap k (B α) c₇ * gen α 0) * gen₂_mul_gen₄ α
      - (algebraMap k (B α) α * algebraMap k (B α) c₆ * gen α 2
        + algebraMap k (B α) c₇ * gen α 3) * gen_mul_self α 0

/-- Multiplying a combination of the eight monomials by $x_3$ gives another one. -/
@[category API, AMS 13 16]
theorem combo_mul_gen₃ (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) :
    combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ * gen α 2
      = combo α 0 0 0 c₀ 0 0 (c₁ - α * c₂) 0 := by
  simp only [combo, map_zero, map_sub, map_mul]
  linear_combination
    (algebraMap k (B α) c₂ + algebraMap k (B α) c₅ * gen α 0) * gen₂_mul_gen₃ α
      + (algebraMap k (B α) c₃ + algebraMap k (B α) c₆ * gen α 0) * gen_mul_self α 2
      + (algebraMap k (B α) c₄ + algebraMap k (B α) c₇ * gen α 0) * rel_x₃x₄ α
      - algebraMap k (B α) α * algebraMap k (B α) c₅ * gen α 2 * gen_mul_self α 0

/-- Multiplying a combination of the eight monomials by $x_4$ gives another one. -/
@[category API, AMS 13 16]
theorem combo_mul_gen₄ (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) :
    combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ * gen α 3
      = combo α 0 0 0 0 c₀ 0 0 (c₁ - c₂) := by
  simp only [combo, map_zero, map_sub]
  linear_combination
    (algebraMap k (B α) c₂ + algebraMap k (B α) c₅ * gen α 0) * gen₂_mul_gen₄ α
      + (algebraMap k (B α) c₃ + algebraMap k (B α) c₆ * gen α 0) * rel_x₃x₄ α
      + (algebraMap k (B α) c₄ + algebraMap k (B α) c₇ * gen α 0) * gen_mul_self α 3
      - algebraMap k (B α) c₅ * gen α 3 * gen_mul_self α 0

/-- The $k$-span of the eight monomials is closed under multiplication by every generator. -/
@[category API, AMS 13 16]
theorem exists_combo_mul_gen (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) (j : Fin 4) :
    ∃ e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ : k,
      combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ * gen α j
        = combo α e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ := by
  fin_cases j
  · exact ⟨0, c₀, 0, 0, 0, c₂, c₃, c₄, combo_mul_gen₁ α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇⟩
  · exact ⟨0, 0, c₀, 0, 0, c₁, -(α * c₃), -c₄, combo_mul_gen₂ α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇⟩
  · exact ⟨0, 0, 0, c₀, 0, 0, c₁ - α * c₂, 0, combo_mul_gen₃ α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇⟩
  · exact ⟨0, 0, 0, 0, c₀, 0, 0, c₁ - c₂, combo_mul_gen₄ α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇⟩

/-- The spanning half of the basis statement: the eight monomials $1$; $x_1, x_2, x_3, x_4$;
$x_1x_2, x_1x_3, x_1x_4$ span $B_\alpha$ over $k$. -/
@[category API, AMS 13 16]
theorem exists_combo (α : k) (u : B α) :
    ∃ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k, u = combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a, 0, 0, 0, 0, 0, 0, 0, by simp [combo]⟩
  | add p q hp hq =>
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, ha⟩ := hp
    obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, hb⟩ := hq
    refine ⟨a₀ + b₀, a₁ + b₁, a₂ + b₂, a₃ + b₃, a₄ + b₄, a₅ + b₅, a₆ + b₆, a₇ + b₇, ?_⟩
    rw [map_add, ha, hb]
    simp only [combo, map_add]
    ring
  | mul_X p j hp =>
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, ha⟩ := hp
    obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, he⟩ :=
      exists_combo_mul_gen α a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ j
    refine ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, ?_⟩
    rw [map_mul, ha]
    exact he

/-- The model map reads off the eight coefficients of a combination of the eight monomials. -/
@[category API, AMS 13 16]
theorem toModel_combo (α : k) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k) :
    toModel α (combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇)
      = ⟨c₀, ![c₁, c₂, c₃, c₄], ![c₅, c₆, c₇]⟩ := by
  refine Model.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [combo, modelVals]

/-- The independence half of the basis statement: a vanishing combination of the eight monomials
has vanishing coefficients. -/
@[category API, AMS 13 16]
theorem combo_eq_zero (α : k) {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : k}
    (h : combo α c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 ∧ c₆ = 0 ∧ c₇ = 0 := by
  have h' : (⟨c₀, ![c₁, c₂, c₃, c₄], ![c₅, c₆, c₇]⟩ : Model α) = 0 := by
    rw [← toModel_combo, h, map_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Model.const h'
  · simpa using congrFun (congrArg Model.lin h') 0
  · simpa using congrFun (congrArg Model.lin h') 1
  · simpa using congrFun (congrArg Model.lin h') 2
  · simpa using congrFun (congrArg Model.lin h') 3
  · simpa using congrFun (congrArg Model.quad h') 0
  · simpa using congrFun (congrArg Model.quad h') 1
  · simpa using congrFun (congrArg Model.quad h') 2

/-- The differential $d_i = \begin{pmatrix} x_1 & \alpha^i x_3 \\ x_4 & x_2 \end{pmatrix}$ of the
complex $\boldsymbol{C}$ of [Lemma 2.2], as a matrix over $B_\alpha$. -/
def d (α : k) (i : ℕ) : Matrix (Fin 2) (Fin 2) (B α) :=
  !![gen α 0, algebraMap k (B α) (α ^ i) * gen α 2; gen α 3, gen α 1]

/-- Consecutive differentials compose to zero, the computation $d_i d_{i+1} = 0$ from the proof
of [Lemma 2.2]. All seven defining relations are used. -/
@[category API, AMS 13 16]
theorem d_mul_d (α : k) (i : ℕ) : d α i * d α (i + 1) = 0 := by
  have hsq₀ : gen α 0 * gen α 0 = 0 := by rw [← sq]; exact gen_sq α 0
  have hsq₁ : gen α 1 * gen α 1 = 0 := by rw [← sq]; exact gen_sq α 1
  have h₃₄ := rel_x₃x₄ α
  have h₁₄ := rel_x₁x₄ α
  have h₁₃ := rel_x₁x₃ α
  have hpow : algebraMap k (B α) (α ^ (i + 1))
      = algebraMap k (B α) (α ^ i) * algebraMap k (B α) α := by
    rw [← map_mul, ← pow_succ]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [d, hpow, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination hsq₀ + algebraMap k (B α) (α ^ i) * h₃₄
  · linear_combination algebraMap k (B α) (α ^ i) * h₁₃
  · linear_combination h₁₄
  · linear_combination
      algebraMap k (B α) (α ^ i) * algebraMap k (B α) α * h₃₄ + hsq₁

/-- The $B_\alpha$-module $L = M \otimes_A B$ of [Section 2]. The complex of [Lemma 2.2] stays
exact after applying $- \otimes_A B$, so $L$ is the image of the map $B_\alpha^2 \to B_\alpha^2$
given by the differential `JorgensenSega.d α 0`. -/
def L (α : k) : Submodule (B α) (Fin 2 → B α) := LinearMap.range (Matrix.mulVecLin (d α 0))

/-- The ideal $J_q = (x_1 - x_2,\ x_1 - \alpha^q x_3,\ x_1 - x_4)$ of $B_\alpha$, the reduction
modulo $x_5$ of the ideal $J_q$ of [Section 3]. -/
def J (α : k) (q : ℤ) : Ideal (B α) :=
  Ideal.span {gen α 0 - gen α 1, gen α 0 - α ^ q • gen α 2, gen α 0 - gen α 3}

/-- The $B_\alpha$-module $T_q = B_\alpha/J_q$ of [Section 3], the reduction modulo $x_5$ of
$A_\alpha/J_q$. It has Hilbert series $1 + t$. -/
abbrev T (α : k) (q : ℤ) : Type u := B α ⧸ J α q

/-- $L$ is a finitely generated $B_\alpha$-module, being the image of a map out of
$B_\alpha^2$. -/
instance (α : k) : Module.Finite (B α) (L α) :=
  Module.Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (Matrix.mulVecLin (d α 0)))

instance (α : k) : Module.Finite (B α) (ULift.{v} (L α)) :=
  Module.Finite.equiv ULift.moduleEquiv.symm

instance (α : k) (q : ℤ) : Module.Finite (B α) (ULift.{v} (T α q)) :=
  Module.Finite.equiv ULift.moduleEquiv.symm

/-- `JorgensenSega.L`, lifted to `Type (max u v)`, as an object of the category of
$B_\alpha$-modules. -/
abbrev Lcat (α : k) : ModuleCat.{max u v} (B α) := ModuleCat.of _ (ULift.{v} (L α))

/-- `JorgensenSega.T`, lifted to `Type (max u v)`, as an object of the category of
$B_\alpha$-modules. -/
abbrev Tcat (α : k) (q : ℤ) : ModuleCat.{max u v} (B α) := ModuleCat.of _ (ULift.{v} (T α q))

/-- Composition of morphisms. This project already uses `≫` for an asymptotic comparison of
sequences, so categorical composition needs a notation of its own here. -/
local infixr:80 " ⊚ " => CategoryTheory.CategoryStruct.comp

/-- The free $B_\alpha$-module $B_\alpha^2$, lifted to `Type (max u v)`. Every term of the
complex $\boldsymbol{C}$ of [Lemma 2.2] is a copy of it. -/
abbrev Fr (α : k) : ModuleCat.{max u v} (B α) := ModuleCat.of _ (ULift.{v} (Fin 2 → B α))

instance (α : k) : Module.Projective (B α) (ULift.{v} (Fin 2 → B α)) :=
  Module.Projective.of_equiv (ULift.moduleEquiv (R := B α) (M := Fin 2 → B α)).symm

/-- A square matrix over $B_\alpha$, read as an endomorphism of `JorgensenSega.Fr`. -/
def frMap (α : k) (M : Matrix (Fin 2) (Fin 2) (B α)) : Fr.{u, v} α ⟶ Fr.{u, v} α :=
  ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ ULift.moduleEquiv.toLinearMap)

@[category API, AMS 13 16 18, simp]
theorem frMap_apply (α : k) (M : Matrix (Fin 2) (Fin 2) (B α)) (x : ULift.{v} (Fin 2 → B α)) :
    (frMap.{u, v} α M).hom x = ULift.up (M.mulVec x.down) := rfl

@[category API, AMS 13 16 18, simp]
theorem frMap_comp (α : k) (M N : Matrix (Fin 2) (Fin 2) (B α)) :
    (frMap.{u, v} α M ⊚ frMap.{u, v} α N) = frMap α (N * M) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp [frMap]

@[category API, AMS 13 16 18, simp]
theorem frMap_zero (α : k) : frMap.{u, v} α 0 = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp [frMap]

/-- The complex $\boldsymbol{F} = \boldsymbol{C}_{\ge 0}$ of [Section 2.6]: every term is
$B_\alpha^2$, and the differential from degree $n+1$ to degree $n$ is $d_{n+1}$. -/
def cx (α : k) : ChainComplex (ModuleCat.{max u v} (B α)) ℕ :=
  ChainComplex.of (fun _ => Fr.{u, v} α) (fun n => frMap α (d α (n + 1)))
    (fun n => by rw [frMap_comp, d_mul_d, frMap_zero])

@[category API, AMS 13 16 18, simp]
theorem cx_d (α : k) (n : ℕ) : (cx.{u, v} α).d (n + 1) n = frMap α (d α (n + 1)) := by
  simp [cx]

/-- The augmentation $\boldsymbol{F} \to L$, given in degree $0$ by $d_0$ corestricted to its
image $L$. -/
def π (α : k) : cx.{u, v} α ⟶ (ChainComplex.single₀ _).obj (Lcat.{u, v} α) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
        (Matrix.mulVecLin (d α 0)).rangeRestrict ∘ₗ ULift.moduleEquiv.toLinearMap), by
      rw [cx_d]
      have h : d α 0 * d α 1 = 0 := by simpa using d_mul_d α 0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      refine ULift.ext _ _ (Subtype.ext ?_)
      show (d α 0).mulVec ((d α 1).mulVec x.down) = (0 : Fin 2 → B α)
      rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]⟩

/-- One half of [Lemma 2.2], the half that says $\boldsymbol{C}$ is a complex: the image of
$d_{i+1}$ lies in the kernel of $d_i$. -/
@[category API, AMS 13 16]
theorem range_le_ker (α : k) (i : ℕ) :
    LinearMap.range (Matrix.mulVecLin (d α (i + 1)))
      ≤ LinearMap.ker (Matrix.mulVecLin (d α i)) := by
  rintro _ ⟨z, rfl⟩
  show (d α i).mulVec ((d α (i + 1)).mulVec z) = 0
  rw [Matrix.mulVec_mulVec, d_mul_d, Matrix.zero_mulVec]

/-- The first component of $d_i$ applied to a vector. -/
@[category API, AMS 13 16]
theorem d_mulVec_zero (α : k) (i : ℕ) (w : Fin 2 → B α) :
    (d α i).mulVec w 0 = gen α 0 * w 0 + algebraMap k (B α) (α ^ i) * gen α 2 * w 1 := by
  simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]

/-- The second component of $d_i$ applied to a vector. -/
@[category API, AMS 13 16]
theorem d_mulVec_one (α : k) (i : ℕ) (w : Fin 2 → B α) :
    (d α i).mulVec w 1 = gen α 3 * w 0 + gen α 1 * w 1 := by
  simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]

/-- Combinations with equal coefficients are equal. -/
@[category API, AMS 13 16]
theorem combo_congr (α : k) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : k}
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃) (h₄ : a₄ = b₄)
    (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
    combo α a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ = combo α b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-- The first row of $d_i$ evaluated on a pair of combinations of the eight monomials. -/
@[category API, AMS 13 16]
theorem row₁_combo (α : k) (i : ℕ) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : k) :
    gen α 0 * combo α a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
        + algebraMap k (B α) (α ^ i) * gen α 2 * combo α b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      = combo α 0 a₀ 0 (α ^ i * b₀) 0 a₂ (a₃ + α ^ i * (b₁ - α * b₂)) a₄ := by
  rw [mul_comm (gen α 0), combo_mul_gen₁,
    show algebraMap k (B α) (α ^ i) * gen α 2 * combo α b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      = algebraMap k (B α) (α ^ i) * (combo α b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ * gen α 2) from by ring,
    combo_mul_gen₃]
  simp only [combo, map_add, map_mul, map_sub, map_zero]
  ring

/-- The second row of $d_i$ evaluated on a pair of combinations of the eight monomials. -/
@[category API, AMS 13 16]
theorem row₂_combo (α : k) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : k) :
    gen α 3 * combo α a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ + gen α 1 * combo α b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      = combo α 0 0 b₀ 0 a₀ b₁ (-(α * b₃)) (a₁ - a₂ - b₄) := by
  rw [mul_comm (gen α 3), combo_mul_gen₄, mul_comm (gen α 1), combo_mul_gen₂]
  simp only [combo, map_neg, map_mul, map_sub, map_zero]
  ring

/-- The other half of [Lemma 2.2]: an element of the kernel of $d_i$ is in the image of
$d_{i+1}$.

Write the kernel element as a pair $(u, v)$ of combinations of the eight monomials, with
coefficients $a_0, \dots, a_7$ and $b_0, \dots, b_7$. Expanding the two rows of $d_i$ with
`JorgensenSega.row₁_combo` and `JorgensenSega.row₂_combo` and applying
`JorgensenSega.combo_eq_zero` gives
$$a_0 = a_2 = a_4 = b_0 = b_1 = b_3 = 0, \quad a_3 = \alpha^{i+1}b_2, \quad b_4 = a_1,$$
with the six coefficients of degree two unconstrained since $\mathfrak{m}^3 = 0$. So the kernel
is eight dimensional. The preimage below solves the resulting $2 \times 2$ system; the only step
that uses $\alpha \ne 0$ is the coefficient $-b_6/\alpha$, which is what produces the monomial
$x_1x_3$ in the second coordinate. Infinite order is nowhere needed. -/
@[category API, AMS 13 16]
theorem ker_le_range (α : k) (hα : α ≠ 0) (i : ℕ) :
    LinearMap.ker (Matrix.mulVecLin (d α i))
      ≤ LinearMap.range (Matrix.mulVecLin (d α (i + 1))) := by
  intro w hw
  have hw' : (d α i).mulVec w = 0 := hw
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, hu⟩ := exists_combo α (w 0)
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, hv⟩ := exists_combo α (w 1)
  have hw0 : combo α 0 a₀ 0 (α ^ i * b₀) 0 a₂ (a₃ + α ^ i * (b₁ - α * b₂)) a₄ = 0 := by
    rw [← row₁_combo α i, ← hu, ← hv, ← d_mulVec_zero]
    exact congrFun hw' 0
  have hw1 : combo α 0 0 b₀ 0 a₀ b₁ (-(α * b₃)) (a₁ - a₂ - b₄) = 0 := by
    rw [← row₂_combo α, ← hu, ← hv, ← d_mulVec_one]
    exact congrFun hw' 1
  obtain ⟨-, ha₀, -, -, -, ha₂, hmix, ha₄⟩ := combo_eq_zero α hw0
  obtain ⟨-, -, hb₀, -, -, hb₁, hb₃, hlast⟩ := combo_eq_zero α hw1
  have hb₃' : b₃ = 0 := (mul_eq_zero.1 (neg_eq_zero.1 hb₃)).resolve_left hα
  have ha₃ : a₃ = α ^ (i + 1) * b₂ := by linear_combination hmix - α ^ i * hb₁
  have hb₄ : b₄ = a₁ := by linear_combination -hlast - ha₂
  subst ha₀
  subst ha₂
  subst ha₄
  subst hb₀
  subst hb₁
  subst hb₃'
  subst ha₃
  subst hb₄
  have key0 : (d α (i + 1)).mulVec
      ![combo α b₄ 0 a₅ (a₆ - α ^ (i + 1) * b₅) a₇ 0 0 0,
        combo α b₂ b₅ 0 (-(b₆ / α)) (-(a₅ + b₇)) 0 0 0] 0 = w 0 := by
    rw [d_mulVec_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [row₁_combo α (i + 1), hu]
    refine combo_congr α ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have key1 : (d α (i + 1)).mulVec
      ![combo α b₄ 0 a₅ (a₆ - α ^ (i + 1) * b₅) a₇ 0 0 0,
        combo α b₂ b₅ 0 (-(b₆ / α)) (-(a₅ + b₇)) 0 0 0] 1 = w 1 := by
    rw [d_mulVec_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [row₂_combo α, hv]
    refine combo_congr α ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · ring
    · ring
    · ring
    · ring
    · ring
    · ring
    · field_simp
    · ring
  refine ⟨![combo α b₄ 0 a₅ (a₆ - α ^ (i + 1) * b₅) a₇ 0 0 0,
    combo α b₂ b₅ 0 (-(b₆ / α)) (-(a₅ + b₇)) 0 0 0], ?_⟩
  funext j
  fin_cases j
  · exact key0
  · exact key1

/-- [Lemma 2.2] The complex $\boldsymbol{C}$ is exact at every spot. -/
@[category research solved, AMS 13 16]
theorem ker_eq_range (α : k) (hα : α ≠ 0) (i : ℕ) :
    LinearMap.ker (Matrix.mulVecLin (d α i))
      = LinearMap.range (Matrix.mulVecLin (d α (i + 1))) :=
  le_antisymm (ker_le_range α hα i) (range_le_ker α i)

/-- The universe lift detects zero. -/
@[category API, AMS 13 16 18]
theorem up_eq_zero_iff (α : k) (w : Fin 2 → B α) :
    (ULift.up w : ULift.{v} (Fin 2 → B α)) = 0 ↔ w = 0 :=
  ⟨fun h => congrArg ULift.down h, fun h => congrArg ULift.up h⟩

/-- `JorgensenSega.ker_eq_range` transported through the universe lift and stated for elements,
which is the form the homology API consumes. -/
@[category API, AMS 13 16 18]
theorem exists_mulVec_iff (α : k) (hα : α ≠ 0) (i : ℕ) (x : ULift.{v} (Fin 2 → B α)) :
    (∃ y : ULift.{v} (Fin 2 → B α), ULift.up ((d α (i + 1)).mulVec y.down) = x)
      ↔ (d α i).mulVec x.down = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    show (d α i).mulVec ((d α (i + 1)).mulVec z.down) = 0
    rw [Matrix.mulVec_mulVec, d_mul_d, Matrix.zero_mulVec]
  · intro hx
    have hx' : x.down ∈ LinearMap.ker (Matrix.mulVecLin (d α i)) := hx
    rw [ker_eq_range α hα i] at hx'
    obtain ⟨z, hz⟩ := hx'
    exact ⟨ULift.up z, congrArg ULift.up hz⟩

/-- The differential out of degree $1$, with the indices in literal form. -/
@[category API, AMS 13 16 18, simp]
theorem cx_d_one_zero (α : k) : (cx.{u, v} α).d 1 0 = frMap.{u, v} α (d α 1) := cx_d α 0

set_option backward.isDefEq.respectTransparency.types false in
/-- The augmentation in degree $0$ is $d_0$ corestricted to its image. -/
@[category API, AMS 13 16 18]
theorem π_f_zero (α : k) :
    (π.{u, v} α).f 0 = ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
      (Matrix.mulVecLin (d α 0)).rangeRestrict ∘ₗ ULift.moduleEquiv.toLinearMap) := by
  simp only [π, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  rfl

/-- The augmentation kills exactly the kernel of $d_0$. -/
@[category API, AMS 13 16 18, simp]
theorem mem_ker_π_f_zero (α : k) (x : ULift.{v} (Fin 2 → B α)) :
    ((π.{u, v} α).f 0).hom x = 0 ↔ (d α 0).mulVec x.down = 0 := by
  rw [π_f_zero]
  constructor
  · intro hx
    exact congrArg (fun y => ((ULift.down y : L α) : Fin 2 → B α)) hx
  · intro hx
    exact ULift.ext _ _ (Subtype.ext hx)

/-- Exactness in the form the homology API produces it, away from degree $0$. -/
@[category API, AMS 13 16 18]
theorem exists_frMap_iff (α : k) (hα : α ≠ 0) (i : ℕ) (x : ULift.{v} (Fin 2 → B α)) :
    (∃ y : ULift.{v} (Fin 2 → B α), (frMap.{u, v} α (d α (i + 1))).hom y = x)
      ↔ (frMap.{u, v} α (d α i)).hom x = 0 :=
  (exists_mulVec_iff α hα i x).trans (up_eq_zero_iff α _).symm

/-- Exactness in the form the homology API produces it, in degree $0$. -/
@[category API, AMS 13 16 18]
theorem exists_frMap_iff_π (α : k) (hα : α ≠ 0) (x : ULift.{v} (Fin 2 → B α)) :
    (∃ y : ULift.{v} (Fin 2 → B α), (frMap.{u, v} α (d α 1)).hom y = x)
      ↔ ((π.{u, v} α).f 0).hom x = 0 :=
  (exists_mulVec_iff α hα 0 x).trans (mem_ker_π_f_zero α x).symm

/-- The augmentation is surjective, since $L$ is by definition the image of $d_0$. -/
@[category API, AMS 13 16 18]
theorem π_f_zero_surjective (α : k) : Function.Surjective ((π.{u, v} α).f 0).hom := by
  rintro ⟨⟨w, z, hz⟩⟩
  exact ⟨ULift.up z, by rw [π_f_zero]; exact ULift.ext _ _ (Subtype.ext hz)⟩

/-- [Lemma 2.2] The augmentation $\boldsymbol{F} \to L$ is a quasi-isomorphism.

In degree $0$ this says that $\pi_0$ is surjective, which holds by the definition of $L$ as the
image of $d_0$, and that its kernel, which is the kernel of $d_0$, is the image of $d_1$. In
degree $n+1$ it says that $\boldsymbol{F}$ is exact at $n+1$, the target being exact there
because it is concentrated in degree $0$. Both reduce to
`JorgensenSega.exists_mulVec_iff`. -/
@[category API, AMS 13 16 18]
theorem res_quasiIso (α : k) (hα : α ≠ 0) : QuasiIso (π.{u, v} α) where
  quasiIsoAt m := by
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        CategoryTheory.ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
        ext x
        simp only [LinearMap.mem_range, LinearMap.mem_ker,
          HomologicalComplex.shortComplexFunctor'_obj_f,
          HomologicalComplex.shortComplexFunctor'_map_τ₂, cx_d_one_zero]
        exact exists_frMap_iff_π α hα x
      · rw [ModuleCat.epi_iff_surjective]
        exact π_f_zero_surjective α
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 1 + 1) (m + 1) m (by simp) (by simp),
        CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
      ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker,
        HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g, cx_d]
      exact exists_frMap_iff α hα (m + 1) x

/-- The complex $\boldsymbol{F}$ with its augmentation is a projective resolution of $L$. This is
[Lemma 2.2]; it needs $\alpha \ne 0$, since for $\alpha = 0$ the relation $x_2x_3 = 0$ puts
$(0, x_1x_3)$ in the kernel of $d_i$ but out of the image of $d_{i+1}$. -/
def res (α : k) (hα : α ≠ 0) : CategoryTheory.ProjectiveResolution (Lcat.{u, v} α) where
  complex := cx α
  π := π α
  projective _ := inferInstanceAs (CategoryTheory.Projective (Fr.{u, v} α))
  quasiIso := res_quasiIso α hα

/-- The image $\bar{x}_1$ of $x_1$ in $T_q$. Together with $1$ it is a $k$-basis of $T_q$. -/
def xbar (α : k) (q : ℤ) : T α q := Ideal.Quotient.mk (J α q) (gen α 0)

@[category API, AMS 13 16]
theorem sub_gen₂_mem_J (α : k) (q : ℤ) : gen α 0 - gen α 1 ∈ J α q :=
  Ideal.subset_span (by simp)

@[category API, AMS 13 16]
theorem sub_gen₃_mem_J (α : k) (q : ℤ) : gen α 0 - α ^ q • gen α 2 ∈ J α q :=
  Ideal.subset_span (by simp)

@[category API, AMS 13 16]
theorem sub_gen₄_mem_J (α : k) (q : ℤ) : gen α 0 - gen α 3 ∈ J α q :=
  Ideal.subset_span (by simp)

/-- Scalars that differ by an element of $J_q$ act in the same way on $T_q$. -/
@[category API, AMS 13 16]
theorem smul_eq_smul_of_sub_mem (α : k) (q : ℤ) {b b' : B α} (h : b - b' ∈ J α q) (y : T α q) :
    b • y = b' • y := by
  induction y using Submodule.Quotient.induction_on with
  | H c =>
    show Ideal.Quotient.mk (J α q) (b * c) = Ideal.Quotient.mk (J α q) (b' * c)
    rw [Ideal.Quotient.eq, show b * c - b' * c = (b - b') * c from by ring]
    exact Ideal.mul_mem_right c _ h

/-- $x_1$ annihilates $\bar{x}_1$, because $x_1^2 = 0$. -/
@[category API, AMS 13 16]
theorem gen₁_smul_xbar (α : k) (q : ℤ) : gen α 0 • xbar α q = 0 := by
  have h : gen α 0 * gen α 0 = 0 := by rw [← sq]; exact gen_sq α 0
  show Ideal.Quotient.mk (J α q) (gen α 0 * gen α 0) = 0
  rw [h, map_zero]

/-- $x_3$ annihilates $\bar{x}_1$: on $T_q$ the element $\alpha^q x_3$ acts as $x_1$. -/
@[category API, AMS 13 16]
theorem gen₃_smul_xbar (α : k) (hα : α ≠ 0) (q : ℤ) : gen α 2 • xbar α q = 0 := by
  have h := smul_eq_smul_of_sub_mem α q (sub_gen₃_mem_J α q) (xbar α q)
  rw [gen₁_smul_xbar, smul_assoc] at h
  exact (smul_eq_zero.1 h.symm).resolve_left (zpow_ne_zero _ hα)

/-- The four values in $k[\varepsilon]$ used to detect $\bar{x}_1 \ne 0$. -/
def dualVals (α : k) (q : ℤ) : Fin 4 → TrivSqZeroExt k k :=
  ![TrivSqZeroExt.inr 1, TrivSqZeroExt.inr 1, TrivSqZeroExt.inr (α ^ (-q)), TrivSqZeroExt.inr 1]

/-- A $k$-algebra map $B_\alpha \to k[\varepsilon]$, $\varepsilon^2 = 0$, sending
$x_1, x_2, x_4 \mapsto \varepsilon$ and $x_3 \mapsto \alpha^{-q}\varepsilon$. Every defining
relation of $B_\alpha$ is a quadric, so it is killed automatically. -/
def toDual (α : k) (q : ℤ) : B α →ₐ[k] TrivSqZeroExt k k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (dualVals α q)) <| by
    intro a ha
    have hle : Ideal.span (relations α) ≤
        RingHom.ker (MvPolynomial.aeval (dualVals α q) :
          MvPolynomial (Fin 4) k →ₐ[k] TrivSqZeroExt k k).toRingHom := by
      rw [Ideal.span_le]
      rintro r hr
      simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [RingHom.mem_ker, dualVals, sq, DualNumber.eps_mul_eps, mul_assoc]
    exact hle ha

@[category API, AMS 13 16, simp]
theorem toDual_gen (α : k) (q : ℤ) (i : Fin 4) : toDual α q (gen α i) = dualVals α q i := by
  simp [toDual, gen, Ideal.Quotient.liftₐ, dualVals]

/-- The map to $k[\varepsilon]$ kills $J_q$. -/
@[category API, AMS 13 16]
theorem J_le_ker_toDual (α : k) (hα : α ≠ 0) (q : ℤ) :
    J α q ≤ RingHom.ker (toDual α q : B α →+* TrivSqZeroExt k k) := by
  rw [J, Ideal.span_le]
  rintro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp [RingHom.mem_ker, dualVals, TrivSqZeroExt.ext_iff, smul_eq_mul, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero q hα)]

/-- $\bar{x}_1 \ne 0$: the map to $k[\varepsilon]$ kills $J_q$ but sends $x_1$ to
$\varepsilon$. -/
@[category API, AMS 13 16]
theorem xbar_ne_zero (α : k) (hα : α ≠ 0) (q : ℤ) : xbar α q ≠ 0 := by
  intro hc
  have h0 : toDual α q (gen α 0) = 0 :=
    J_le_ker_toDual α hα q ((Submodule.Quotient.mk_eq_zero _).1 hc)
  rw [toDual_gen] at h0
  simp [dualVals, TrivSqZeroExt.ext_iff] at h0

/-- A scalar multiple of $\bar{x}_1$ vanishes only if the scalar does. -/
@[category API, AMS 13 16]
theorem eq_zero_of_mkT_eq_zero (α : k) (hα : α ≠ 0) (q : ℤ) {r : k}
    (h : Ideal.Quotient.mk (J α q) (algebraMap k (B α) r * gen α 0) = 0) : r = 0 := by
  have h0 : toDual α q (algebraMap k (B α) r * gen α 0) = 0 :=
    J_le_ker_toDual α hα q ((Submodule.Quotient.mk_eq_zero _).1 h)
  rw [map_mul, AlgHom.commutes, toDual_gen] at h0
  simpa [dualVals, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] using
    congrArg TrivSqZeroExt.snd h0

/-- Every element of $T_q$ is $a + b\,\bar{x}_1$ with $a, b \in k$: the algebra $T_q$ is the ring
of dual numbers, with $k$-basis $1, \bar{x}_1$. -/
@[category API, AMS 13 16]
theorem exists_repr (α : k) (hα : α ≠ 0) (q : ℤ) (y : T α q) :
    ∃ a b : k, y = Ideal.Quotient.mk (J α q)
      (algebraMap k (B α) a + algebraMap k (B α) b * gen α 0) := by
  have hsq : gen α 0 * gen α 0 = 0 := by rw [← sq]; exact gen_sq α 0
  have h₃' : gen α 0 - algebraMap k (B α) (α ^ q) * gen α 2 ∈ J α q := by
    rw [← Algebra.smul_def]
    exact sub_gen₃_mem_J α q
  have hinv : algebraMap k (B α) (α ^ (-q)) * algebraMap k (B α) (α ^ q) = 1 := by
    rw [← map_mul, ← zpow_add₀ hα, neg_add_cancel, zpow_zero, map_one]
  have e₀ : Ideal.Quotient.mk (J α q) (gen α 0)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) 1 * gen α 0) := by rw [map_one, one_mul]
  have e₁ : Ideal.Quotient.mk (J α q) (gen α 1)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) 1 * gen α 0) := by
    rw [map_one, one_mul]
    exact Ideal.Quotient.eq.2 (by simpa using neg_mem (sub_gen₂_mem_J α q))
  have e₃ : Ideal.Quotient.mk (J α q) (gen α 3)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) 1 * gen α 0) := by
    rw [map_one, one_mul]
    exact Ideal.Quotient.eq.2 (by simpa using neg_mem (sub_gen₄_mem_J α q))
  have e₂ : Ideal.Quotient.mk (J α q) (gen α 2)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) (α ^ (-q)) * gen α 0) := by
    refine Ideal.Quotient.eq.2 ?_
    have key : gen α 2 - algebraMap k (B α) (α ^ (-q)) * gen α 0
        = -(algebraMap k (B α) (α ^ (-q))
            * (gen α 0 - algebraMap k (B α) (α ^ q) * gen α 2))
          + (1 - algebraMap k (B α) (α ^ (-q)) * algebraMap k (B α) (α ^ q)) * gen α 2 := by
      ring
    rw [key, hinv, sub_self, zero_mul, add_zero]
    exact neg_mem (Ideal.mul_mem_left _ _ h₃')
  have hgen : ∀ j : Fin 4, ∃ c : k,
      Ideal.Quotient.mk (J α q) (Ideal.Quotient.mk (Ideal.span (relations α)) (X j))
        = Ideal.Quotient.mk (J α q) (algebraMap k (B α) c * gen α 0) := by
    intro j
    fin_cases j
    · exact ⟨1, e₀⟩
    · exact ⟨1, e₁⟩
    · exact ⟨α ^ (-q), e₂⟩
    · exact ⟨1, e₃⟩
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction r using MvPolynomial.induction_on with
  | C a => exact ⟨a, 0, by rw [mk_C, map_zero, zero_mul, add_zero]⟩
  | add r r' hr hr' =>
    obtain ⟨a, b, hab⟩ := hr
    obtain ⟨a', b', hab'⟩ := hr'
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add, map_add, hab, hab', ← map_add]
    refine congrArg _ ?_
    rw [map_add, map_add]
    ring
  | mul_X r j hr =>
    obtain ⟨a, b, hab⟩ := hr
    obtain ⟨c, hc⟩ := hgen j
    refine ⟨0, a * c, ?_⟩
    rw [map_mul, map_mul, hab, hc, ← map_mul]
    refine congrArg _ ?_
    rw [map_zero, zero_add, map_mul]
    have key : (algebraMap k (B α) a + algebraMap k (B α) b * gen α 0)
        * (algebraMap k (B α) c * gen α 0)
        = algebraMap k (B α) a * algebraMap k (B α) c * gen α 0
          + algebraMap k (B α) b * algebraMap k (B α) c * (gen α 0 * gen α 0) := by ring
    rw [key, hsq, mul_zero, add_zero]

/-- Multiplication by $x_1$ on $T_q$ has kernel equal to its image, both equal to
$k\,\bar{x}_1$. -/
@[category API, AMS 13 16]
theorem exists_smul_eq (α : k) (hα : α ≠ 0) (q : ℤ) {y : T α q} (hy : gen α 0 • y = 0) :
    ∃ z : T α q, gen α 0 • z = y := by
  have hsq : gen α 0 * gen α 0 = 0 := by rw [← sq]; exact gen_sq α 0
  obtain ⟨a, b, rfl⟩ := exists_repr α hα q y
  have hexp : gen α 0 • Ideal.Quotient.mk (J α q)
      (algebraMap k (B α) a + algebraMap k (B α) b * gen α 0)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) a * gen α 0) := by
    have hB : gen α 0 * (algebraMap k (B α) a + algebraMap k (B α) b * gen α 0)
        = algebraMap k (B α) a * gen α 0 := by
      have key : gen α 0 * (algebraMap k (B α) a + algebraMap k (B α) b * gen α 0)
          = algebraMap k (B α) a * gen α 0
            + algebraMap k (B α) b * (gen α 0 * gen α 0) := by ring
      rw [key, hsq, mul_zero, add_zero]
    exact congrArg (Ideal.Quotient.mk (J α q)) hB
  rw [hexp] at hy
  have ha : a = 0 := eq_zero_of_mkT_eq_zero α hα q hy
  subst ha
  refine ⟨Ideal.Quotient.mk (J α q) (algebraMap k (B α) b), ?_⟩
  have hB : gen α 0 * algebraMap k (B α) b
      = algebraMap k (B α) 0 + algebraMap k (B α) b * gen α 0 := by
    rw [map_zero, zero_add]
    ring
  exact congrArg (Ideal.Quotient.mk (J α q)) hB

/-- On $T_q$ the element $x_4$ acts as $x_1$. -/
@[category API, AMS 13 16]
theorem gen₄_smul (α : k) (q : ℤ) (y : T α q) : gen α 3 • y = gen α 0 • y :=
  smul_eq_smul_of_sub_mem α q (by simpa using neg_mem (sub_gen₄_mem_J α q)) y

/-- On $T_q$ the element $x_2$ acts as $x_1$. -/
@[category API, AMS 13 16]
theorem gen₂_smul (α : k) (q : ℤ) (y : T α q) : gen α 1 • y = gen α 0 • y :=
  smul_eq_smul_of_sub_mem α q (by simpa using neg_mem (sub_gen₂_mem_J α q)) y

/-- On $T_q$ the element $\alpha^q x_3$ acts as $x_1$. -/
@[category API, AMS 13 16]
theorem gen₃_smul (α : k) (q : ℤ) (n : ℕ) (hn : (n : ℤ) = q) (y : T α q) :
    (algebraMap k (B α) (α ^ n) * gen α 2) • y = gen α 0 • y := by
  refine smul_eq_smul_of_sub_mem α q ?_ y
  have h : algebraMap k (B α) (α ^ n) * gen α 2 = α ^ q • gen α 2 := by
    rw [← hn, zpow_natCast]
    exact (Algebra.smul_def _ _).symm
  rw [h]
  simpa using neg_mem (sub_gen₃_mem_J α q)

/-- A morphism out of the free module $B_\alpha^2$ is determined by the images of the two basis
vectors. -/
@[category API, AMS 13 16 18]
theorem hom_free_apply (α : k) {Y : ModuleCat.{max u v} (B α)} (g : Fr.{u, v} α ⟶ Y)
    (w : Fin 2 → B α) :
    g.hom (ULift.up w)
      = w 0 • g.hom (ULift.up ![1, 0]) + w 1 • g.hom (ULift.up ![0, 1]) := by
  have hw : (ULift.up w : ULift.{v} (Fin 2 → B α))
      = w 0 • ULift.up ![1, 0] + w 1 • ULift.up ![0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hw, map_add, map_smul, map_smul]

/-- Acting by `b` on a class is multiplying by `b` before taking the class. -/
@[category API, AMS 13 16, simp]
theorem smul_mkT (α : k) (q : ℤ) (b w : B α) :
    b • Ideal.Quotient.mk (J α q) w = Ideal.Quotient.mk (J α q) (b * w) := rfl

/-- Modulo $J_q$ the element $x_4$ may be replaced by $x_1$. -/
@[category API, AMS 13 16]
theorem mkT_gen₄_mul (α : k) (q : ℤ) (w : B α) :
    Ideal.Quotient.mk (J α q) (gen α 3 * w) = Ideal.Quotient.mk (J α q) (gen α 0 * w) := by
  refine Ideal.Quotient.eq.2 ?_
  rw [show gen α 3 * w - gen α 0 * w = -((gen α 0 - gen α 3) * w) from by ring]
  exact neg_mem (Ideal.mul_mem_right w _ (sub_gen₄_mem_J α q))

/-- Modulo $J_q$ the element $x_2$ may be replaced by $x_1$. -/
@[category API, AMS 13 16]
theorem mkT_gen₂_mul (α : k) (q : ℤ) (w : B α) :
    Ideal.Quotient.mk (J α q) (gen α 1 * w) = Ideal.Quotient.mk (J α q) (gen α 0 * w) := by
  refine Ideal.Quotient.eq.2 ?_
  rw [show gen α 1 * w - gen α 0 * w = -((gen α 0 - gen α 1) * w) from by ring]
  exact neg_mem (Ideal.mul_mem_right w _ (sub_gen₂_mem_J α q))

/-- Modulo $J_q$ the element $\alpha^m x_3$ may be replaced by $\alpha^{m-q} x_1$. -/
@[category API, AMS 13 16]
theorem mkT_gen₃_mul (α : k) (hα : α ≠ 0) (q : ℤ) (m : ℕ) (w : B α) :
    Ideal.Quotient.mk (J α q) (algebraMap k (B α) (α ^ m) * gen α 2 * w)
      = Ideal.Quotient.mk (J α q) (algebraMap k (B α) (α ^ ((m : ℤ) - q)) * gen α 0 * w) := by
  have h₃' : gen α 0 - algebraMap k (B α) (α ^ q) * gen α 2 ∈ J α q := by
    rw [← Algebra.smul_def]
    exact sub_gen₃_mem_J α q
  have hpow : algebraMap k (B α) (α ^ ((m : ℤ) - q)) * algebraMap k (B α) (α ^ q)
      = algebraMap k (B α) (α ^ m) := by
    rw [← map_mul, ← zpow_add₀ hα, sub_add_cancel, zpow_natCast]
  refine Ideal.Quotient.eq.2 ?_
  rw [show algebraMap k (B α) (α ^ m) * gen α 2 * w
      - algebraMap k (B α) (α ^ ((m : ℤ) - q)) * gen α 0 * w
      = -(algebraMap k (B α) (α ^ ((m : ℤ) - q)) * w
          * (gen α 0 - algebraMap k (B α) (α ^ q) * gen α 2))
        + (algebraMap k (B α) (α ^ m)
            - algebraMap k (B α) (α ^ ((m : ℤ) - q)) * algebraMap k (B α) (α ^ q))
          * gen α 2 * w from by ring, hpow, sub_self, zero_mul, zero_mul, add_zero]
  exact neg_mem (Ideal.mul_mem_left _ _ h₃')

/-- If $\alpha$ has infinite multiplicative order then no positive power of it is $1$. -/
@[category API, AMS 13 16]
theorem zpow_ne_one (α : k) (hord : ∀ m : ℕ, 0 < m → α ^ m ≠ 1) {t : ℤ} (ht : 0 < t) :
    α ^ t ≠ 1 := by
  lift t to ℕ using ht.le with m
  rw [zpow_natCast]
  exact hord m (by exact_mod_cast ht)

/-- The morphism $B_\alpha^2 \to T_q$ sending the two basis vectors to `a` and `b`. -/
def toT (α : k) (q : ℤ) (a b : T α q) : Fr.{u, v} α ⟶ Tcat.{u, v} α q :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    ((LinearMap.proj 0 : (Fin 2 → B α) →ₗ[B α] B α).smulRight a +
      (LinearMap.proj 1 : (Fin 2 → B α) →ₗ[B α] B α).smulRight b) ∘ₗ
    ULift.moduleEquiv.toLinearMap)

@[category API, AMS 13 16 18, simp]
theorem toT_apply (α : k) (q : ℤ) (a b : T α q) (w : Fin 2 → B α) :
    (toT.{u, v} α q a b).hom (ULift.up w) = ULift.up (w 0 • a + w 1 • b) := rfl

/-- Two morphisms out of the free module agree as soon as they agree on the two basis
vectors. -/
@[category API, AMS 13 16 18]
theorem hom_ext_free (α : k) {Y : ModuleCat.{max u v} (B α)} {g g' : Fr.{u, v} α ⟶ Y}
    (h₁ : g.hom (ULift.up ![1, 0]) = g'.hom (ULift.up ![1, 0]))
    (h₂ : g.hom (ULift.up ![0, 1]) = g'.hom (ULift.up ![0, 1])) : g = g' := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have e := hom_free_apply α g x.down
  have e' := hom_free_apply α g' x.down
  rw [h₁, h₂] at e
  exact e.trans e'.symm

/-- The cocycle of degree $q$ used to exhibit a nonzero class in
$\operatorname{Ext}^q_{B_\alpha}(L, T_q)$: the map $B_\alpha^2 \to T_q$ sending the first basis
vector to $\bar{x}_1$ and the second to $0$. -/
def cocycle (α : k) (q : ℤ) : Fr.{u, v} α ⟶ Tcat.{u, v} α q :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    (LinearMap.proj 0 : (Fin 2 → B α) →ₗ[B α] B α).smulRight (xbar α q) ∘ₗ
      ULift.moduleEquiv.toLinearMap)

@[category API, AMS 13 16 18, simp]
theorem cocycle_apply (α : k) (q : ℤ) (w : Fin 2 → B α) :
    (cocycle.{u, v} α q).hom (ULift.up w) = ULift.up (w 0 • xbar α q) := rfl

/-- `JorgensenSega.cocycle` really is a cocycle: it kills the incoming differential, because
both $x_1$ and $x_3$ annihilate $\bar{x}_1$ in $T_q$. -/
@[category API, AMS 13 16 18]
theorem d_comp_cocycle (α : k) (hα : α ≠ 0) (q : ℤ) (n : ℕ) :
    ((cx.{u, v} α).d (n + 1) n ⊚ cocycle.{u, v} α q) = 0 := by
  rw [cx_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine ULift.ext _ _ ?_
  show ((d α (n + 1)).mulVec x.down) 0 • xbar α q = (0 : T α q)
  have hval : ((d α (n + 1)).mulVec x.down) 0
      = x.down 0 * gen α 0 + x.down 1 * (algebraMap k (B α) (α ^ (n + 1)) * gen α 2) := by
    simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]
    ring
  rw [hval, add_smul, mul_smul, mul_smul, gen₁_smul_xbar,
    mul_smul, gen₃_smul_xbar α hα q, smul_zero, smul_zero, smul_zero, add_zero]

/-- $B_\alpha$ is generated as a $k$-algebra by the images $x_1, x_2, x_3, x_4$ of the
variables. -/
@[category API, AMS 13 16]
theorem adjoin_range_gen (α : k) : Algebra.adjoin k (Set.range (gen α)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => simpa using Subalgebra.add_mem _ hp hq
  | mul_X p i hp => simpa [gen] using Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- [Section 2] $B_\alpha$ is a finite dimensional $k$-algebra. It is generated by the four
square-zero elements $x_1, x_2, x_3, x_4$, hence is generated by finitely many integral elements.
The article computes its Hilbert series to be $1 + 4t + 3t^2$, so $\lambda(B_\alpha) = 8$. -/
@[category API, AMS 13 16]
theorem finite (α : k) : Module.Finite k (B α) := by
  have hfg : (Algebra.adjoin k (Set.range (gen α))).toSubmodule.FG :=
    fg_adjoin_of_finite (Set.finite_range _) <| by
      rintro _ ⟨i, rfl⟩
      exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [gen_sq]⟩
  rw [adjoin_range_gen] at hfg
  exact ⟨hfg⟩

set_option maxHeartbeats 1000000 in
/-- The half of [Corollary 3.3(2)] that makes $T_q$ an admissible test module for the conjecture:
$\operatorname{Ext}^i_{B_\alpha}(L, T_q)$ vanishes in every degree above $q$.

Over the resolution `JorgensenSega.res` a class of degree $i$ is a map $B_\alpha^2 \to T_q$, that
is a pair $(a, b)$ of dual numbers. The cocycle condition forces the constant terms of $a$ and $b$
to vanish, because $\alpha^{i+1-q} \ne 1$; what is left is a $2 \times 2$ system with determinant
$1 - \alpha^{i-q} \ne 0$, so the class is a coboundary. Both uses of $\alpha$ having infinite
order are exactly here. -/
@[category API, AMS 13 16 18]
theorem subsingleton_ext_of_lt (α : k) (hα : α ≠ 0) (hord : ∀ n : ℕ, 0 < n → α ^ n ≠ 1) (q : ℤ)
    (hq : 0 < q) (i : ℕ) (hi : q < (i : ℤ)) :
    Subsingleton (Ext (Lcat.{u, v} α) (Tcat.{u, v} α q) i) := by
  obtain ⟨n, rfl⟩ : ∃ m : ℕ, i = m + 1 := ⟨i - 1, by omega⟩
  have hsq : gen α 0 * gen α 0 = 0 := by rw [← sq]; exact gen_sq α 0
  have hden : α ^ (((n + 1 : ℕ) : ℤ) - q) - 1 ≠ 0 :=
    sub_ne_zero.2 (zpow_ne_one α hord (by omega))
  have hdent : α ^ (((n + 1 + 1 : ℕ) : ℤ) - q) - 1 ≠ 0 :=
    sub_ne_zero.2 (zpow_ne_one α hord (by omega))
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : Ext (Lcat.{u, v} α) (Tcat.{u, v} α q) (n + 1), z = 0 by rw [h x, h y]
  intro z
  obtain ⟨f, hf, rfl⟩ : ∃ (f : Fr.{u, v} α ⟶ Tcat.{u, v} α q)
      (hf : ((res.{u, v} α hα).complex.d (n + 1 + 1) (n + 1) ⊚ f) = 0),
      (res.{u, v} α hα).extMk f (n + 1 + 1) rfl hf = z :=
    (res.{u, v} α hα).extMk_surjective z (n + 1 + 1) rfl
  refine ((res.{u, v} α hα).extMk_eq_zero_iff f (n + 1 + 1) rfl hf n rfl).mpr ?_
  have hf' : (frMap.{u, v} α (d α (n + 1 + 1)) ⊚ f) = 0 := by
    rw [← cx_d α (n + 1)]
    exact hf
  -- the two columns of the differentials
  have M₁ : ∀ m : ℕ, (d α m).mulVec ![(1 : B α), 0] = ![gen α 0, gen α 3] := by
    intro m
    ext j
    fin_cases j <;> simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]
  have M₂ : ∀ m : ℕ, (d α m).mulVec ![(0 : B α), 1]
      = ![algebraMap k (B α) (α ^ m) * gen α 2, gen α 1] := by
    intro m
    ext j
    fin_cases j <;> simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]
  -- coordinates of the cocycle `f`
  obtain ⟨a₀, a₁, ha⟩ := exists_repr α hα q (f.hom (ULift.up ![(1 : B α), 0])).down
  obtain ⟨b₀, b₁, hb⟩ := exists_repr α hα q (f.hom (ULift.up ![(0 : B α), 1])).down
  have evf : ∀ w : Fin 2 → B α, f.hom (ULift.up ((d α (n + 1 + 1)).mulVec w)) = 0 := fun w =>
    congrArg (fun m : Fr.{u, v} α ⟶ Tcat.{u, v} α q => m.hom (ULift.up w)) hf'
  have e₁ := evf ![1, 0]
  have e₂ := evf ![0, 1]
  rw [M₁, hom_free_apply] at e₁
  rw [M₂, hom_free_apply] at e₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e₁ e₂
  have d₁ : gen α 0 • (f.hom (ULift.up ![(1 : B α), 0])).down
      + gen α 3 • (f.hom (ULift.up ![(0 : B α), 1])).down = 0 := congrArg ULift.down e₁
  have d₂ : (algebraMap k (B α) (α ^ (n + 1 + 1)) * gen α 2)
        • (f.hom (ULift.up ![(1 : B α), 0])).down
      + gen α 1 • (f.hom (ULift.up ![(0 : B α), 1])).down = 0 := congrArg ULift.down e₂
  rw [ha, hb, smul_mkT, smul_mkT, ← map_add] at d₁
  rw [ha, hb, smul_mkT, smul_mkT, ← map_add] at d₂
  -- the cocycle condition on constant terms
  rw [map_add, mkT_gen₄_mul, ← map_add,
    show gen α 0 * (algebraMap k (B α) a₀ + algebraMap k (B α) a₁ * gen α 0)
        + gen α 0 * (algebraMap k (B α) b₀ + algebraMap k (B α) b₁ * gen α 0)
      = algebraMap k (B α) (a₀ + b₀) * gen α 0
        + (algebraMap k (B α) a₁ + algebraMap k (B α) b₁) * (gen α 0 * gen α 0) from by
      rw [map_add]; ring, hsq, mul_zero, add_zero] at d₁
  rw [map_add, mkT_gen₂_mul, mkT_gen₃_mul α hα, ← map_add,
    show algebraMap k (B α) (α ^ (((n + 1 + 1 : ℕ) : ℤ) - q)) * gen α 0
          * (algebraMap k (B α) a₀ + algebraMap k (B α) a₁ * gen α 0)
        + gen α 0 * (algebraMap k (B α) b₀ + algebraMap k (B α) b₁ * gen α 0)
      = algebraMap k (B α) (α ^ (((n + 1 + 1 : ℕ) : ℤ) - q) * a₀ + b₀) * gen α 0
        + (algebraMap k (B α) (α ^ (((n + 1 + 1 : ℕ) : ℤ) - q)) * algebraMap k (B α) a₁
            + algebraMap k (B α) b₁) * (gen α 0 * gen α 0) from by
      rw [map_add, map_mul]; ring, hsq, mul_zero, add_zero] at d₂
  have h₁ : a₀ + b₀ = 0 := eq_zero_of_mkT_eq_zero α hα q d₁
  have h₂ : α ^ (((n + 1 + 1 : ℕ) : ℤ) - q) * a₀ + b₀ = 0 := eq_zero_of_mkT_eq_zero α hα q d₂
  have ha₀ : a₀ = 0 := by
    have : (α ^ (((n + 1 + 1 : ℕ) : ℤ) - q) - 1) * a₀ = 0 := by linear_combination h₂ - h₁
    exact (mul_eq_zero.1 this).resolve_left hdent
  have hb₀ : b₀ = 0 := by linear_combination h₁ - ha₀
  subst ha₀
  subst hb₀
  -- solve the remaining `2 × 2` system
  refine ⟨toT.{u, v} α q (Ideal.Quotient.mk (J α q)
      (algebraMap k (B α) ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))))
    (Ideal.Quotient.mk (J α q)
      (algebraMap k (B α) (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1)))), ?_⟩
  rw [show (res.{u, v} α hα).complex.d (n + 1) n = frMap.{u, v} α (d α (n + 1)) from cx_d α n]
  refine hom_ext_free α ?_ ?_
  · show (toT.{u, v} α q _ _).hom (ULift.up ((d α (n + 1)).mulVec ![(1 : B α), 0])) = _
    rw [M₁, toT_apply]
    refine ULift.ext _ _ ?_
    rw [ha]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_mkT, ← map_add]
    rw [map_add, mkT_gen₄_mul, ← map_add]
    refine congrArg _ ?_
    rw [map_zero, zero_add]
    have hce : (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1) + (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1)) = a₁ := by ring
    rw [show gen α 0 * algebraMap k (B α) ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))
          + gen α 0 * algebraMap k (B α) (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))
        = algebraMap k (B α) ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1) + (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))) * gen α 0 from by rw [map_add]; ring, hce]
  · show (toT.{u, v} α q _ _).hom (ULift.up ((d α (n + 1)).mulVec ![(0 : B α), 1])) = _
    rw [M₂, toT_apply]
    refine ULift.ext _ _ ?_
    rw [hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_mkT, ← map_add]
    rw [map_add, mkT_gen₂_mul, mkT_gen₃_mul α hα, ← map_add]
    refine congrArg _ ?_
    rw [map_zero, zero_add]
    have hbe : α ^ (((n + 1 : ℕ) : ℤ) - q) * ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1)) + (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1)) = b₁ := by
      field_simp
      ring
    rw [show algebraMap k (B α) (α ^ (((n + 1 : ℕ) : ℤ) - q)) * gen α 0 * algebraMap k (B α) ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))
          + gen α 0 * algebraMap k (B α) (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))
        = algebraMap k (B α) (α ^ (((n + 1 : ℕ) : ℤ) - q) * ((b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1)) + (a₁ - (b₁ - a₁) / (α ^ (((n + 1 : ℕ) : ℤ) - q) - 1))) * gen α 0 from by
        rw [map_add, map_mul]; ring, hbe]

/-- The half of [Corollary 3.3(2)] that refutes the conjecture:
$\operatorname{Ext}^q_{B_\alpha}(L, T_q)$ is nonzero, in the degree $q$, which can be taken
arbitrarily large.

The class is exhibited explicitly. Over the resolution `JorgensenSega.res` of $L$, the map
`JorgensenSega.cocycle` sending the first basis vector of $B_\alpha^2$ to $\bar{x}_1$ and the
second to $0$ is a cocycle in degree $q$. It is not a coboundary: if it were $g \circ d_q$, then
evaluating at the two basis vectors and using that $x_2$, $x_4$ and $\alpha^q x_3$ all act on
$T_q$ as $x_1$ gives $x_1 g(e_1) + x_1 g(e_2)$ equal both to $\bar{x}_1$ and to $0$, whereas
$\bar{x}_1 \ne 0$.

No part of [Corollary 3.3(2)] is used; the argument runs off the resolution directly. Note also
that $\alpha$ need not have infinite order for this half. -/
@[category API, AMS 13 16 18]
theorem not_subsingleton_ext_self (α : k) (hα : α ≠ 0) (q : ℤ) (hq : 0 < q) (i : ℕ)
    (hi : (i : ℤ) = q) :
    ¬ Subsingleton (Ext (Lcat.{u, v} α) (Tcat.{u, v} α q) i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 1 := ⟨i - 1, by omega⟩
  intro hsub
  have hf : ((res.{u, v} α hα).complex.d (n + 1 + 1) (n + 1) ⊚ cocycle.{u, v} α q) = 0 :=
    d_comp_cocycle α hα q (n + 1)
  refine (?_ : (res.{u, v} α hα).extMk (cocycle α q) (n + 1 + 1) rfl hf ≠ 0) (Subsingleton.elim _ _)
  intro hzero
  obtain ⟨g, hg⟩ : ∃ g : Fr.{u, v} α ⟶ Tcat.{u, v} α q,
      ((res.{u, v} α hα).complex.d (n + 1) n ⊚ g) = cocycle.{u, v} α q :=
    ((res.{u, v} α hα).extMk_eq_zero_iff (cocycle α q) (n + 1 + 1) rfl hf n rfl).mp hzero
  rw [show (res.{u, v} α hα).complex.d (n + 1) n = frMap.{u, v} α (d α (n + 1)) from cx_d α n] at hg
  have m₁ : (d α (n + 1)).mulVec ![(1 : B α), 0] = ![gen α 0, gen α 3] := by
    ext j
    fin_cases j <;> simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]
  have m₂ : (d α (n + 1)).mulVec ![(0 : B α), 1]
      = ![algebraMap k (B α) (α ^ (n + 1)) * gen α 2, gen α 1] := by
    ext j
    fin_cases j <;> simp [Matrix.mulVec, d, Matrix.vecHead, Matrix.vecTail]
  -- Composition in `ModuleCat` and both maps are definitional, so evaluating `hg` at a vector
  -- `w` directly gives the equation below.
  have ev : ∀ w : Fin 2 → B α,
      g.hom (ULift.up ((d α (n + 1)).mulVec w)) = ULift.up (w 0 • xbar α q) := fun w =>
    congrArg (fun m : Fr.{u, v} α ⟶ Tcat.{u, v} α q => m.hom (ULift.up w)) hg
  have e₁ := ev ![1, 0]
  have e₂ := ev ![0, 1]
  simp only [Matrix.cons_val_zero, one_smul] at e₁ e₂
  rw [m₁, hom_free_apply] at e₁
  rw [m₂, hom_free_apply] at e₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e₁ e₂
  have s₄ : ∀ y : ULift.{v} (T α q), gen α 3 • y = gen α 0 • y :=
    fun y => ULift.ext _ _ (gen₄_smul α q y.down)
  have s₂ : ∀ y : ULift.{v} (T α q), gen α 1 • y = gen α 0 • y :=
    fun y => ULift.ext _ _ (gen₂_smul α q y.down)
  have s₃ : ∀ y : ULift.{v} (T α q),
      (algebraMap k (B α) (α ^ (n + 1)) * gen α 2) • y = gen α 0 • y :=
    fun y => ULift.ext _ _ (gen₃_smul α q (n + 1) hi y.down)
  rw [s₄] at e₁
  rw [s₃, s₂] at e₂
  exact xbar_ne_zero α hα q (congrArg ULift.down (e₁.symm.trans e₂))

/-- [Corollary 3.3(2)] Let $\alpha$ be a nonzero element of infinite multiplicative order and let
$q > 0$. In the degrees $i \ge q$,
$$\operatorname{Ext}^i_{B_\alpha}(L, T_q) \ne 0 \iff i = q ,$$
so the cohomology vanishes for $i \gg 0$ while being nonzero in degree $q$, which can be made
arbitrarily large. This is what the refutation uses, and it is the two halves
`JorgensenSega.subsingleton_ext_of_lt` and `JorgensenSega.not_subsingleton_ext_self` put
together.

The corollary in the article is stronger: it settles every degree, giving
$\operatorname{Ext}^i_{B_\alpha}(L, T_q) \ne 0$ exactly for $i \in \{0,\ q - 1,\ q\}$. The
non-vanishing in the degrees $0$ and $q - 1$ is not needed here and is not proved. -/
@[category research solved, AMS 13 16 18]
theorem ext_L_T_ne_zero (α : k) (hα : α ≠ 0) (hord : ∀ n : ℕ, 0 < n → α ^ n ≠ 1) (q : ℤ)
    (hq : 0 < q) (i : ℕ) (hi : q ≤ (i : ℤ)) :
    ¬ Subsingleton (Ext (Lcat.{u, v} α) (Tcat.{u, v} α q) i) ↔ (i : ℤ) = q := by
  refine ⟨fun hne => ?_, not_subsingleton_ext_self α hα q hq i⟩
  by_contra hiq
  exact hne (subsingleton_ext_of_lt α hα hord q hq i (by omega))

end

set_option linter.style.haveILetI false in
/-- The refutation of the Auslander Conjecture, with the universes named so that $\mathbb{Q}$ can
be lifted into each of them. `AuslanderConjecture` below is exactly this statement. -/
@[category research solved, AMS 13 16 18]
theorem counterexample.{u₁, u₂, u₃} :
    ¬ ∀ (R : Type u₁) (A : Type u₂)
      [CommRing R] [IsArtinianRing R]
      [Ring A] [Algebra R A] [Module.Finite R A],
        ∀ (X : ModuleCat.{max u₂ u₃} A) [Module.Finite A X],
          ∃ n > 0,
            ∀ (Y : ModuleCat.{max u₂ u₃} A) [Module.Finite A Y],
            (∃ m : ℕ, ∀ i : ℕ, m ≤ i → Subsingleton (Ext X Y i)) →
              ∀ i : ℕ, n ≤ i → Subsingleton (Ext X Y i) := by
  intro h
  -- `ℚ`, lifted to the universe of `A`, has an element of infinite multiplicative order.
  obtain ⟨α, hα, hord⟩ : ∃ α : ULift.{u₂} ℚ, α ≠ 0 ∧ ∀ n : ℕ, 0 < n → α ^ n ≠ 1 := by
    refine ⟨(ULift.ringEquiv (R := ℚ)).symm 2, fun hc => ?_, fun n hn hc => ?_⟩
    · have h' := congrArg (⇑(ULift.ringEquiv (R := ℚ))) hc
      simp only [RingEquiv.apply_symm_apply, map_zero] at h'
      norm_num at h'
    · have h' := congrArg (⇑(ULift.ringEquiv (R := ℚ))) hc
      simp only [map_pow, RingEquiv.apply_symm_apply, map_one] at h'
      exact (one_lt_pow₀ one_lt_two hn.ne').ne' h'
  -- `B α` is a finite dimensional algebra over `ℚ`, hence over `ℚ` lifted to the universe of `R`.
  have hkA : Module.Finite (ULift.{u₂} ℚ) (B α) := finite α
  have hQk : Module.Finite ℚ (ULift.{u₂} ℚ) :=
    Module.Finite.of_surjective (Algebra.linearMap ℚ (ULift.{u₂} ℚ)) fun x => ⟨x.down, rfl⟩
  have hQA : Module.Finite ℚ (B α) := Module.Finite.trans (ULift.{u₂} ℚ) (B α)
  letI : Algebra (ULift.{u₁} ℚ) ℚ := ULift.algebra' ℚ ℚ
  letI : Algebra (ULift.{u₁} ℚ) (B α) := ULift.algebra' ℚ (B α)
  have hRQ : Module.Finite (ULift.{u₁} ℚ) ℚ :=
    Module.Finite.of_surjective (Algebra.linearMap (ULift.{u₁} ℚ) ℚ) fun x => ⟨ULift.up x, rfl⟩
  have hRA : Module.Finite (ULift.{u₁} ℚ) (B α) := Module.Finite.trans ℚ (B α)
  -- Specialise the conjecture to the Artin algebra `B α` and the module `L`.
  obtain ⟨n, -, hn⟩ := h (ULift.{u₁} ℚ) (B α) (Lcat.{u₂, u₃} α)
  -- `T q` for `q = n + 1` has vanishing cohomology in degrees `> q`, so it satisfies the
  -- hypothesis of the conjecture, but its cohomology is nonzero in degree `q = n + 1 ≥ n`.
  refine not_subsingleton_ext_self.{u₂, u₃} α hα ((n : ℤ) + 1) (by omega) (n + 1) (by omega) ?_
  exact hn (Tcat.{u₂, u₃} α ((n : ℤ) + 1))
    ⟨n + 2, fun i hi => subsingleton_ext_of_lt.{u₂, u₃} α hα hord _ (by omega) i (by omega)⟩
    (n + 1) (by omega)

end JorgensenSega


/--
# Auslander Conjecture (disproved):
Let $A$ be an Artin algebra over a commutative Artinian ring $R$.
For any finitely generated left $A$-module $X$ there is an integer $n > 0$ such that
for any finitely generated left $A$-module $Y$ satisfying $\operatorname{Ext}^i_A(X,Y) = 0$ for $i ≫ 0$
it follows that $\operatorname{Ext}^i_A(X,Y) = 0$ for any $i ≥ n$.
-/

@[category research solved, AMS 16 18]
theorem AuslanderConjecture :
  ¬ ∀ (R : Type*) (A : Type*)
    [CommRing R] [IsArtinianRing R]
    [Ring A] [Algebra R A] [Module.Finite R A],
      ∀ (X : ModuleCat A) [Module.Finite A X],
        ∃ n > 0,
          ∀ (Y : ModuleCat A) [Module.Finite A Y],
          (∃ m : ℕ, ∀ i : ℕ, m ≤ i → Subsingleton (Ext X Y i)) →
            ∀ i : ℕ, n ≤ i → Subsingleton (Ext X Y i) :=
  JorgensenSega.counterexample

end Arxiv.«math.0306001»
