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
# Ben Green's Open Problem 68

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.68)
- [Gr14] Green, B., *Approximate algebraic structure*. Proceedings of the ICM 2014, Vol. I,
  Kyung Moon Sa, Seoul (2014), 341--367. [arXiv:1404.0093](https://arxiv.org/abs/1404.0093)
- [Vo90] Voloch, J. F., *Arcs in projective planes over prime fields*. J. Geom. 38 (1990),
  198--200.
- [BaLa19] Ball, S. and Lavrauw, M., *Arcs in finite projective spaces*. EMS Surv. Math. Sci. 6
  (2019), 133--172. [arXiv:1908.10772](https://arxiv.org/abs/1908.10772)
-/

@[expose] public section

namespace Green68

/--
`MeetsLinesInAtMost k A` says that the set `A` of points of the affine space $\mathbb{F}_p^d$ meets
every line in at most `k` points. Equivalently, no `k + 1` points of `A` are collinear.
-/
def MeetsLinesInAtMost {d p : ℕ} [Fact p.Prime] (k : ℕ) (A : Finset (Fin d → ZMod p)) : Prop :=
  ∀ s ⊆ A, s.card = k + 1 → ¬ Collinear (ZMod p) (s : Set (Fin d → ZMod p))

/--
`numOffCurve F A` is the number of points $a$ of `A` that are not on the curve $F = 0$, that is,
with $F(a) \ne 0$.
-/
noncomputable def numOffCurve {d p : ℕ} (F : MvPolynomial (Fin d) (ZMod p))
    (A : Finset (Fin d → ZMod p)) : ℕ :=
  (A.filter fun a ↦ MvPolynomial.eval a F ≠ 0).card

/--
`maxNoThreeCollinear d p` is $f_d(p)$, the size of the largest subset of $\mathbb{F}_p^d$ with no
three points on a line. The set of possible sizes is nonempty (it contains $0$) and bounded by
$p^d$, so the supremum is the maximum.
-/
noncomputable def maxNoThreeCollinear (d p : ℕ) [Fact p.Prime] : ℕ :=
  sSup {k : ℕ | ∃ A : Finset (Fin d → ZMod p), A.card = k ∧ MeetsLinesInAtMost 2 A}

/-- A set with at most `k` points meets every line in at most `k` points. -/
@[category API, AMS 5 51]
theorem meetsLinesInAtMost_of_card_le {d p : ℕ} [Fact p.Prime] {k : ℕ}
    {A : Finset (Fin d → ZMod p)} (h : A.card ≤ k) : MeetsLinesInAtMost k A := by
  intro s hs hcard
  exfalso
  have := Finset.card_le_card hs
  omega

/-- `numOffCurve F A = 0` holds if and only if $F$ vanishes at every point of `A`. -/
@[category API, AMS 5 14]
theorem numOffCurve_eq_zero_iff {d p : ℕ} (F : MvPolynomial (Fin d) (ZMod p))
    (A : Finset (Fin d → ZMod p)) :
    numOffCurve F A = 0 ↔ ∀ a ∈ A, MvPolynomial.eval a F = 0 := by
  simp [numOffCurve, Finset.filter_eq_empty_iff]

/--
Suppose that $A \subset \mathbb{F}_p^2$ is a set meeting every line in at most 2 points. Is it true
that all except $o(p)$ points of $A$ lie on a cubic curve?

Such sets are called arcs. We read "cubic curve" as the zero set of a nonzero polynomial of total
degree at most $3$ in two variables over $\mathbb{F}_p$. This includes conics and lines, and unions
of these. The $o(p)$ is uniform in $A$: for every $\varepsilon > 0$ and every large prime $p$, every
arc $A$ has all but at most $\varepsilon p$ of its points on one such curve. Green asked a
projective form of this question in [Gr14, Section 4.4]. [Gr24] notes that the question is more
natural in projective space, and that the analogue over $\mathbb{F}_q$ with $q = p^2$ is false,
because of Hermitian quadrics.
-/
@[category research open, question, AMS 5 14 51]
theorem green_68 :
    ∀ ε : ℝ, 0 < ε → ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ∀ A : Finset (Fin 2 → ZMod p), MeetsLinesInAtMost 2 A →
        ∃ F : MvPolynomial (Fin 2) (ZMod p), F ≠ 0 ∧ F.totalDegree ≤ 3 ∧
          (numOffCurve F A : ℝ) ≤ ε * p := by
  sorry

/--
**Voloch's theorem.** If $p$ is an odd prime and $A \subset \mathbb{F}_p^2$ is a set meeting every
line in at most 2 points, with $|A| > \frac{44}{45} p + \frac{8}{9}$, then $A$ lies on a conic
[BaLa19, Theorem 52], due to Voloch [Vo90]. This is the affine form of the theorem for planar arcs
in $\mathrm{PG}(2, p)$: a set of affine points is an arc in $\mathrm{PG}(2, p)$ if and only if it
meets every affine line in at most 2 points, and the affine equation $Q(x, y, 1) = 0$ of a conic
$Q = 0$ through $A$ is a nonzero polynomial of degree at most $2$ vanishing on $A$. We assume $p$
odd, as in [BaLa19, Section 15.3].
-/
@[category research solved, AMS 5 14 51]
theorem green_68.variants.voloch :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ A : Finset (Fin 2 → ZMod p), MeetsLinesInAtMost 2 A →
        (44 : ℝ) / 45 * p + 8 / 9 < A.card →
          ∃ F : MvPolynomial (Fin 2) (ZMod p),
            F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ A, MvPolynomial.eval a F = 0 := by
  sorry

/--
More generally than in `green_68`, one may conjecture that if $A \subset \mathbb{F}_p^2$ meets
every line in $O(1)$ points, then all but $o(p)$ points of $A$ lie on a curve of degree $O(1)$
[Gr24]. We read this as: for every $k$ there is a degree bound $d$ such that, for every
$\varepsilon > 0$ and every large prime $p$, every set meeting each line in at most $k$ points has
all but at most $\varepsilon p$ points on the zero set of a nonzero polynomial of total degree at
most $d$. The degree $d$ depends on $k$, not on $p$ or $\varepsilon$.
-/
@[category research open, AMS 5 14 51]
theorem green_68.variants.bounded_intersection :
    ∀ k : ℕ, ∃ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ∀ A : Finset (Fin 2 → ZMod p), MeetsLinesInAtMost k A →
        ∃ F : MvPolynomial (Fin 2) (ZMod p), F ≠ 0 ∧ F.totalDegree ≤ d ∧
          (numOffCurve F A : ℝ) ≤ ε * p := by
  sorry

/--
Denote by $f_d(p)$ the size of the largest no-three-in-a-line set in $\mathbb{F}_p^d$. Is
$f_4(p) = o(p^3)$?

[Gr24] reports that $f_2(p) \sim p$ and $f_3(p) \sim p^2$, and that the best known upper bound is
$f_4(p) \le (1 - c)p^3$ for a constant $c > 0$, due to Nagy and Szőnyi, a slight improvement of
the trivial bound.
-/
@[category research open, question, AMS 5 51]
theorem green_68.variants.f_four_little_o :
    ∀ ε : ℝ, 0 < ε → ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      (maxNoThreeCollinear 4 p : ℝ) ≤ ε * (p : ℝ) ^ 3 := by
  sorry

/--
Is $f_4(p) = O(p^{2+o(1)})$, where $f_d(p)$ is the size of the largest no-three-in-a-line set in
$\mathbb{F}_p^d$? We read $O(p^{2+o(1)})$ as: for every $\varepsilon > 0$ there is $C$ with
$f_4(p) \le C p^{2+\varepsilon}$ for all primes $p$. This is stronger than
`green_68.variants.f_four_little_o`.
-/
@[category research open, question, AMS 5 51]
theorem green_68.variants.f_four_polynomial :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime],
      (maxNoThreeCollinear 4 p : ℝ) ≤ C * (p : ℝ) ^ (2 + ε) := by
  sorry

/--
Let $\mathrm{PG}(2, q)$ be the projective plane over $\mathbb{F}_q$. Is there a set $B \subset
\mathrm{PG}(2, q)$ (a "blocking set") meeting every line in at least 1, but at most 1000, points?

A question of this kind goes back to Erdős (see [Gr24]). For $q$ not prime such sets exist in many
cases [Gr24]. As $q$ ranges over sufficiently large primes, it is speculated that no such set
exists [Gr24]. We state this speculation. Points of $\mathrm{PG}(2, p)$ are the one-dimensional
subspaces of $\mathbb{F}_p^3$ (`Projectivization`), and lines are the two-dimensional subspaces.
-/
@[category research open, AMS 5 51]
theorem green_68.variants.blocking_set :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ¬ ∃ B : Set (Projectivization (ZMod p) (Fin 3 → ZMod p)),
        ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p), Module.finrank (ZMod p) W = 2 →
          1 ≤ Set.ncard {x ∈ B | x.submodule ≤ W} ∧ Set.ncard {x ∈ B | x.submodule ≤ W} ≤ 1000 := by
  sorry

end Green68
