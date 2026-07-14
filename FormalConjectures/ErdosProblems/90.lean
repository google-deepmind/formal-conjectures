/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 90: The unit distance problem

*Reference:* [erdosproblems.com/90](https://www.erdosproblems.com/90)

The conjecture asks whether every set of $n$ points in $\mathbb{R}^2$ determines at most
$n^{1 + O(1/\log\log n)}$ unit distances. It was **disproved** in May 2026: an internal model at
OpenAI produced a construction beating the conjectured bound, with the proof digested and
human-verified in two arXiv papers:

* W. Sawin, [*An explicit lower bound for the unit distance problem*](https://arxiv.org/abs/2605.20579)
  (2026), giving $u(n) \ge n^{1.014114}/C$ for infinitely many $n$;
* N. Alon, T. F. Bloom, W. T. Gowers, D. Litt, W. Sawin, A. Shankar, J. Tsimerman, V. Wang and
  M. Matchett Wood, [*Remarks on the disproof of the unit distance conjecture*](https://arxiv.org/abs/2605.20695)
  (2026), giving the qualitative form $u(n) \ge n^{1+\varepsilon}$ for some $\varepsilon > 0$.

This file records the main statement (`erdos_90`), the two constructive disproof variants, the
logical implications between them, and the load-bearing reductions of Sawin's proof
(`sawin_lattice_reduction` and `sawin_totally_real_tower`) as further benchmark challenges.
-/

open Filter EuclideanGeometry NumberField
open scoped EuclideanGeometry

namespace Erdos90
open Finset

/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount points | (points : Finset ℝ²) (_ : points.card = n)}

/--
This lemma confirms that the set of possible unit distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem unitDistanceCounts_BddAbove (n : ℕ) : BddAbove <| unitDistanceCounts n := by
  unfold Erdos90.unitDistanceCounts
  unfold unitDistancePairsCount
  use n.choose 2
  rintro _ ⟨points, rfl, rfl⟩
  rw [points.card.choose_two_right]
  gcongr
  refine (card_filter_le _ _).trans_eq ?_
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]


/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)


/--
Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most
$n^{1+O(\frac{1}{\log\log n})}$ many pairs which are distance $1$ apart?

This was
[disproved](https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf)
by an internal model at OpenAI, which constructed (for infinitely many $n$) a set $P$ of $n$ points
in $\mathbb{R}^2$ such that the number of unit distance pairs in $P$ is at least $n^{1+c}$, where
$c > 0$ is an absolute constant.
-/
@[category research solved, AMS 52]
theorem erdos_90 : answer(False) ↔ ∃ (O : ℕ → ℝ) (hO : O =O[atTop] (fun n => 1 / (n : ℝ).log.log)),
    (fun n => (maxUnitDistances n : ℝ)) =ᶠ[atTop] fun (n : ℕ) => (n : ℝ) ^ (1 + O n) := by
  sorry

/--
**Constructive form of the disproof.** There is an absolute constant $c > 0$ such that
infinitely many $n$ admit a configuration realising at least $n^{1+c}$ unit distances.

This is the qualitative content of Theorem 1.1 of Alon–Bloom–Gowers–Litt–Sawin–Shankar–
Tsimerman–Wang–Matchett Wood, [*Remarks on the disproof of the unit distance conjecture*](https://arxiv.org/abs/2605.20695)
(2026). An explicit bound $c \ge 0.014114$ is given by Sawin, [*An explicit lower bound for the
unit distance problem*](https://arxiv.org/abs/2605.20579) (2026); see
`erdos_90.variants.sawin_explicit` below.
-/
@[category research solved, AMS 52]
theorem erdos_90.variants.polynomial_lower_bound :
    ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ (1 + c) ≤ (maxUnitDistances n : ℝ)}.Infinite := by
  sorry

/--
**Sawin's explicit exponent.** The constructive disproof can be realised with $c \ge 0.014114$
(absorbing the implicit constant $C$ of Sawin's Theorem 1 into a slightly smaller exponent for
all large enough $n$). Reference: Theorem 1 of Sawin, [arXiv:2605.20579](https://arxiv.org/abs/2605.20579)
(2026).
-/
@[category research solved, AMS 52]
theorem erdos_90.variants.sawin_explicit :
    {n : ℕ | (n : ℝ) ^ (1.014114 : ℝ) ≤ (maxUnitDistances n : ℝ)}.Infinite := by
  sorry

/-- Sawin's explicit bound implies the qualitative polynomial lower bound, by taking
$c = 0.014114$. -/
@[category test, AMS 52]
theorem erdos_90.variants.sawin_explicit_implies_polynomial_lower_bound :
    type_of% erdos_90.variants.sawin_explicit →
    type_of% erdos_90.variants.polynomial_lower_bound := by
  intro h
  exact ⟨0.014114, by norm_num, by convert h; norm_num⟩

/-- The polynomial lower bound implies the answer to Erdős 90 is `False`: a fixed positive
exponent $c$ is incompatible with the conjectured $O(1 / \log \log n)$ growth. -/
@[category test, AMS 52]
theorem erdos_90.variants.polynomial_lower_bound_implies_erdos_90 :
    type_of% erdos_90.variants.polynomial_lower_bound →
    type_of% erdos_90 := by
  rintro ⟨c, hc, hInf⟩
  refine ⟨fun h => h.elim, fun ⟨O_fn, hO_bigO, hO_eq⟩ => ?_⟩
  -- 1/log(log(n)) → 0, so O_fn = O(1/log log n) implies O_fn → 0
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n : ℝ).log.log) atTop (nhds 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hO_zero : Tendsto O_fn atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp
      (hO_bigO.trans_isLittleO ((Asymptotics.isLittleO_one_iff ℝ).mpr hg))
  -- Eventually u(n) < n^{1+c}, contradicting the infinitely-often lower bound
  have hLt : ∀ᶠ (n : ℕ) in atTop, ¬((n : ℝ) ^ (1 + c) ≤ (maxUnitDistances n : ℝ)) := by
    filter_upwards [hO_eq, hO_zero.eventually (Iio_mem_nhds hc), eventually_ge_atTop 2]
      with n hEq hOLt hn
    rw [not_le, hEq]
    exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  rw [← cofinite_eq_atTop] at hLt
  exact hInf.frequently_cofinite hLt

/--
**Sawin's Lemma 2: lattice geometry of unit distances** (Sawin, [arXiv:2605.20579](https://arxiv.org/abs/2605.20579)).

Let $d \ge 1$, $R \ge 2$, and suppose $\Lambda \subset \mathbb{R}^{2d}$ is a lattice equipped with
an additive embedding $\pi : \Lambda \to \mathbb{R}^2$. Suppose $S \subseteq \Lambda$ is a finite
set of "matching" vectors satisfying $\|v\| \le 1$ and $\|\pi v\| = 1$ for every $v \in S$. Then
there is a finite point set $U \subset \mathbb{R}^2$ with unit-distance density at least
$(1 - 1/R)^{2d}\,\#S$, i.e. $(1-1/R)^{2d}\,\#S\,\#U \le \#\{\text{unit pairs in } U\}$.

This pure geometry-of-numbers reduction is the elementary heart of the disproof.
-/
@[category research solved, AMS 52]
theorem sawin_lattice_reduction
    (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (hR : 2 ≤ R)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2*d))))
    (π : Λ →+ ℝ²) (hπ : Function.Injective π)
    (S : Finset Λ)
    (hS_norm : ∀ v ∈ S, ‖(v : EuclideanSpace ℝ (Fin (2*d)))‖ ≤ 1)
    (hS_proj : ∀ v ∈ S, ‖π v‖ = 1) :
    ∃ U : Finset ℝ², 0 < U.card ∧
      ((1 : ℝ) - 1/R) ^ (2*d) * (S.card : ℝ) * (U.card : ℝ) ≤
        (unitDistancePairsCount U : ℝ) := by
  sorry

/--
**Sawin's Lemmas 11–12 / Remarks Proposition 2.3: the totally real tower.**

There exist $rdBound : \mathbb{R}$ and a *single* infinite set $Q$ of rational primes
$q \equiv 1 \pmod 4$ such that for every $N$ one can find a totally real number field $F/\mathbb{Q}$
of degree $\ge N$ with bounded root discriminant $|disc F|^{1/[F:\mathbb{Q}]} \le rdBound$ in which
*every* prime $q \in Q$ splits completely.

The load-bearing feature is the quantifier order: $Q$ is fixed *before* $F$, so the same primes
split completely in fields of *unbounded* degree. (For a single fixed $F$, Chebotarev already
gives infinitely many completely split primes $\equiv 1 \pmod 4$, so a per-field statement would
be vacuous.) This uniform splitting in an unbounded tower is the key arithmetic input to the
disproof. It is proved as Lemmas 11–12 of Sawin, [arXiv:2605.20579](https://arxiv.org/abs/2605.20579),
and as Proposition 2.3 of the [Remarks](https://arxiv.org/abs/2605.20695) paper, via the
Golod–Shafarevich inequality for pro-$2$ groups together with the Hajir–Maire–Ramakrishna (2003)
tower construction.

A "completely split" rational prime $q$ in $F$ is one for which $(q)$ is the product of exactly
$[F:\mathbb{Q}]$ distinct maximal ideals.
-/
@[category research solved, AMS 11]
theorem sawin_totally_real_tower :
    ∃ (rdBound : ℝ) (Q : Set ℕ), Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  sorry

end Erdos90
