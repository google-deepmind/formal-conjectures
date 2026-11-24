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
# The Morton–Silverman uniform boundedness conjecture

For a number field $K$, dimension $N \ge 1$, and degree $d \ge 2$, a morphism
$f : \mathbb{P}^N \to \mathbb{P}^N$ of degree $d$ over $K$ is given in homogeneous coordinates by
$(N + 1)$ homogeneous degree-$d$ polynomials in $K[X_0, \dots, X_N]$ with no common nonzero zero
over $\overline{K}$. A point $P \in \mathbb{P}^N(K)$ is called *preperiodic* whenever its forward
$f$-orbit is finite.

Douglas G. Northcott (1950) proved that each such morphism has only finitely many $K$-rational
preperiodic points. Patrick Morton and Joseph H. Silverman (1994) conjectured that this finite
count admits a uniform upper bound depending only on $[K : \mathbb{Q}]$, $N$, and $d$. Even for
quadratic polynomials $x \mapsto x^2 + c$ over $\mathbb{Q}$, uniform boundedness remains open;
Bjorn Poonen (1998) conjectured that no rational periodic point of $x^2 + c$ has minimal period
greater than $3$ (which implies at most $9$ rational preperiodic points in
$\mathbb{P}^1(\mathbb{Q})$).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Arithmetic_dynamics)
- [No50] D. G. Northcott, *Periodic points on an algebraic variety*, Ann. of Math. (2) 51 (1950),
  no. 1, 167–177.
- [MS94] P. Morton and J. H. Silverman, *Rational periodic points of rational functions*, Internat.
  Math. Res. Notices 1994 (1994), no. 2, 97–110.
- [Po98] B. Poonen, *The classification of rational preperiodic points of quadratic polynomials
  over $\mathbb{Q}$: a refined conjecture*, Math. Z. 228 (1998), no. 1, 11–29.
-/

@[expose] public section

namespace MortonSilvermanConjecture

/-- An $(N+1)$-tuple $F$ of polynomials in $K[X_0, \dots, X_N]$ defines a *degree-$d$ projective
morphism* $f : \mathbb{P}^N \to \mathbb{P}^N$ over $K$ if every $F_i$ is homogeneous of degree $d$
and $F_0, \dots, F_N$ have no common nonzero zero over $\overline{K}$. -/
def IsProjectiveMorphism (K : Type*) [Field K] (N d : ℕ)
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) : Prop :=
  (∀ i : Fin (N + 1), (F i).IsHomogeneous d) ∧
    ∀ z : Fin (N + 1) → AlgebraicClosure K,
      (∀ i : Fin (N + 1),
        MvPolynomial.eval z (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (F i)) = 0) →
      z = 0

/-- Two nonzero homogeneous coordinate tuples $x, y \in K^{N+1} \setminus \{0\}$ represent the same
point of $\mathbb{P}^N(K)$ if $y = c \cdot x$ for some $c \in K^\times$. -/
def ProjEquiv (K : Type*) [Field K] (N : ℕ) (x y : Fin (N + 1) → K) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ ∃ c : K, c ≠ 0 ∧ y = c • x

/-- A nonzero tuple $x \in K^{N+1} \setminus \{0\}$ represents a *$K$-rational preperiodic point*
of $F$ if two distinct forward iterates $F^m(x)$ and $F^n(x)$ ($m < n$) define the same projective
point in $\mathbb{P}^N(K)$. -/
def IsPreperiodicProjPoint (K : Type*) [Field K] (N : ℕ)
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) (x : Fin (N + 1) → K) : Prop :=
  x ≠ 0 ∧ ∃ m n : ℕ, m < n ∧
    ProjEquiv K N
      ((fun v i ↦ MvPolynomial.eval v (F i))^[m] x)
      ((fun v i ↦ MvPolynomial.eval v (F i))^[n] x)

/-- The squaring map $(X_0^2, X_1^2)$ on $\mathbb{P}^1$ is a degree-$2$ projective morphism over
every field $K$. -/
@[category API, AMS 11 14 37]
theorem isProjectiveMorphism_squaring (K : Type*) [Field K] :
    IsProjectiveMorphism K 1 2 (fun i : Fin 2 ↦ (MvPolynomial.X i) ^ 2) := by
  refine ⟨fun i ↦ ?_, fun z hz ↦ ?_⟩
  · simpa using (MvPolynomial.isHomogeneous_X K i).pow 2
  · ext i
    have hi := hz i
    simp only [map_pow, MvPolynomial.map_X, MvPolynomial.eval_X, sq_eq_zero_iff] at hi
    exact hi

/-- Under $(X_0^2, X_1^2)$ on $\mathbb{P}^1(\mathbb{Q})$, the point $[1 : -1]$ is preperiodic. -/
@[category test, AMS 11 14 37]
theorem isPreperiodicProjPoint_squaring_one_neg_one :
    IsPreperiodicProjPoint ℚ 1 (fun i : Fin 2 ↦ (MvPolynomial.X i) ^ 2) ![1, -1] := by
  let sqMap : (Fin 2 → ℚ) → (Fin 2 → ℚ) :=
    fun v i ↦ MvPolynomial.eval v ((MvPolynomial.X i : MvPolynomial (Fin 2) ℚ) ^ 2)
  have h1 : sqMap^[1] ![1, -1] = ![1, 1] := by
    ext i; fin_cases i <;> simp [sqMap]
  have h2 : sqMap^[2] ![1, -1] = ![1, 1] := by
    change sqMap (sqMap^[1] ![1, -1]) = ![1, 1]
    rw [h1]
    ext i; fin_cases i <;> simp [sqMap]
  have hne : (![(1 : ℚ), 1] : Fin 2 → ℚ) ≠ 0 := by
    intro h0
    have h00 := congrFun h0 0
    norm_num at h00
  refine ⟨?_, 1, 2, by omega, ?_⟩
  · intro h0
    have h00 := congrFun h0 0
    norm_num at h00
  · change ProjEquiv ℚ 1 (sqMap^[1] ![1, -1]) (sqMap^[2] ![1, -1])
    rw [h1, h2]
    exact ⟨hne, hne, 1, one_ne_zero, (one_smul ℚ _).symm⟩

/-- Under $(X_0^2, X_1^2)$ on $\mathbb{P}^1(\mathbb{Q})$, the point $[1 : 2]$ is not
preperiodic. -/
@[category test, AMS 11 14 37]
theorem not_isPreperiodicProjPoint_squaring_one_two :
    ¬ IsPreperiodicProjPoint ℚ 1 (fun i : Fin 2 ↦ (MvPolynomial.X i) ^ 2) ![1, 2] := by
  let sqMap : (Fin 2 → ℚ) → (Fin 2 → ℚ) :=
    fun v i ↦ MvPolynomial.eval v ((MvPolynomial.X i : MvPolynomial (Fin 2) ℚ) ^ 2)
  have hiter : ∀ k : ℕ, ∀ v : Fin 2 → ℚ, sqMap^[k] v = fun i ↦ (v i) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => intro v; ext i; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih v]
      ext i
      simp only [sqMap, map_pow, MvPolynomial.eval_X]
      rw [← pow_mul, pow_succ]
  rintro ⟨_, m, n, hmn, _, _, c, _, hrel⟩
  change sqMap^[n] ![1, 2] = c • sqMap^[m] ![1, 2] at hrel
  rw [hiter m, hiter n] at hrel
  have h0 := congrFun hrel 0
  have h1 := congrFun hrel 1
  simp only [Matrix.cons_val_zero, one_pow, Pi.smul_apply, smul_eq_mul, mul_one,
    Matrix.cons_val_one] at h0 h1
  rw [← h0, one_mul] at h1
  have hpow_lt : (2 : ℚ) ^ (2 ^ m) < (2 : ℚ) ^ (2 ^ n) :=
    pow_lt_pow_right₀ (by norm_num) (Nat.pow_lt_pow_right (by omega) hmn)
  linarith

/-- At degree $d = 1$, the identity morphism $(X_0, X_1)$ on $\mathbb{P}^1(\mathbb{Q})$ has
arbitrarily large finite sets of pairwise inequivalent rational fixed points, showing $d \ge 2$ is
needed in Northcott's theorem and the Morton–Silverman conjecture. -/
@[category test, AMS 11 14 37]
theorem degree_one_unbounded_preperiodic (B : ℕ) :
    ∃ S : Finset (Fin 2 → ℚ),
      (∀ x ∈ S, IsPreperiodicProjPoint ℚ 1 (fun i : Fin 2 ↦ MvPolynomial.X i) x) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ProjEquiv ℚ 1 x y) ∧
      B < S.card := by
  let pt : ℕ → (Fin 2 → ℚ) := fun k ↦ ![1, (k : ℚ)]
  have hpt_inj : Function.Injective pt := fun a b hab ↦ by simpa [pt] using congrFun hab 1
  refine ⟨(Finset.range (B + 1)).map ⟨pt, hpt_inj⟩, ?_, ?_, by simp⟩
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨k, _, rfl⟩
    dsimp
    have hne : pt k ≠ 0 := fun h0 ↦ by simpa [pt] using congrFun h0 0
    refine ⟨hne, 0, 1, by omega, ?_⟩
    have hid1 :
        (fun v i ↦ MvPolynomial.eval v (MvPolynomial.X i : MvPolynomial (Fin 2) ℚ))^[1] (pt k) =
          pt k := by ext i; simp
    rw [Function.iterate_zero_apply, hid1]
    exact ⟨hne, hne, 1, one_ne_zero, (one_smul ℚ (pt k)).symm⟩
  · intro x hx y hy hxy hproj
    rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, _, rfl⟩
    dsimp at hxy hproj
    rcases hproj with ⟨_, _, c, _, hcy⟩
    have hc0 := congrFun hcy 0
    have hc1 := congrFun hcy 1
    simp only [pt, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_one,
      Matrix.cons_val_one] at hc0 hc1
    rw [← hc0, one_mul, Nat.cast_inj] at hc1
    exact hxy (congrArg pt hc1.symm)

/-- **Northcott's Theorem** ([No50]): Every projective morphism $f : \mathbb{P}^N \to \mathbb{P}^N$
of degree $d \ge 2$ ($N \ge 1$) over an algebraic number field $K$ has only finitely many pairwise
inequivalent $K$-rational preperiodic points. -/
@[category research solved, AMS 11 14 37]
theorem northcott_preperiodic_finiteness (K : Type*) [Field K] [NumberField K] (N d : ℕ)
    (hN : 1 ≤ N) (hd : 2 ≤ d) (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)
    (hF : IsProjectiveMorphism K N d F) :
    ∃ B : ℕ, ∀ S : Finset (Fin (N + 1) → K),
      (∀ x ∈ S, IsPreperiodicProjPoint K N F x) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ProjEquiv K N x y) →
      S.card ≤ B := by
  sorry

/-- **Morton–Silverman Uniform Boundedness Conjecture** ([MS94]): For every field degree $D \ge 1$,
projective dimension $N \ge 1$, and morphism degree $d \ge 2$, there exists a constant $B$ such
that for every number field $K$ of degree $[K : \mathbb{Q}] = D$ and every degree-$d$ projective
morphism $f : \mathbb{P}^N \to \mathbb{P}^N$ over $K$, the number of pairwise inequivalent
$K$-rational preperiodic points of $f$ is at most $B$. -/
@[category research open, AMS 11 14 37]
theorem morton_silverman_conjecture (D N d : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hd : 2 ≤ d) :
    ∃ B : ℕ, ∀ (K : Type) [Field K] [NumberField K],
      Module.finrank ℚ K = D →
      ∀ F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K,
        IsProjectiveMorphism K N d F →
        ∀ S : Finset (Fin (N + 1) → K),
          (∀ x ∈ S, IsPreperiodicProjPoint K N F x) →
          (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ProjEquiv K N x y) →
          S.card ≤ B := by
  sorry

/-- **Morton–Silverman Conjecture on $\mathbb{P}^1(\mathbb{Q})$** ([MS94]): For every degree
$d \ge 2$, there exists a constant $B$ depending only on $d$ such that every degree-$d$ projective
morphism $f : \mathbb{P}^1 \to \mathbb{P}^1$ over $\mathbb{Q}$ has at most $B$ pairwise
inequivalent $\mathbb{Q}$-rational preperiodic points. -/
@[category research open, AMS 11 14 37]
theorem morton_silverman_conjecture.variants.rat_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : ℕ, ∀ F : Fin 2 → MvPolynomial (Fin 2) ℚ,
      IsProjectiveMorphism ℚ 1 d F →
      ∀ S : Finset (Fin 2 → ℚ),
        (∀ x ∈ S, IsPreperiodicProjPoint ℚ 1 F x) →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ProjEquiv ℚ 1 x y) →
        S.card ≤ B := by
  sorry

/-- **Poonen's Rational Periodic Point Conjecture** ([Po98]): For every $c \in \mathbb{Q}$, the
quadratic polynomial $F_c(x) = x^2 + c$ has no rational periodic point of minimal period strictly
greater than $3$. -/
@[category research open, AMS 11 14 37]
theorem poonen_quadratic_periodic_conjecture (c x : ℚ)
    (hx : x ∈ Function.periodicPts (fun z : ℚ ↦ z ^ 2 + c)) :
    Function.minimalPeriod (fun z : ℚ ↦ z ^ 2 + c) x ≤ 3 := by
  sorry

/-- **Poonen's Preperiodic Cardinality Conjecture** ([Po98], Corollary 1): For every
$c \in \mathbb{Q}$, the homogenized quadratic polynomial $[X_0 : X_1] \mapsto [X_0^2 + c X_1^2 :
X_1^2]$ on $\mathbb{P}^1(\mathbb{Q})$ has at most $9$ pairwise inequivalent $\mathbb{Q}$-rational
preperiodic points (counting $\infty = [1 : 0]$).

Note: The explicit upper bound $9$ comes from [Po98], Corollary 1, as a consequence of
`poonen_quadratic_periodic_conjecture`. -/
@[category research open, AMS 11 14 37]
theorem morton_silverman_conjecture.variants.poonen_quadratic_bound (c : ℚ)
    (S : Finset (Fin 2 → ℚ))
    (hpre : ∀ x ∈ S,
      IsPreperiodicProjPoint ℚ 1
        ![(MvPolynomial.X 0) ^ 2 + MvPolynomial.C c * (MvPolynomial.X 1) ^ 2,
          (MvPolynomial.X 1) ^ 2] x)
    (hineq : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ProjEquiv ℚ 1 x y) :
    S.card ≤ 9 := by
  sorry

end MortonSilvermanConjecture
