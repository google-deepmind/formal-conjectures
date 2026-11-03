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
# The Lane–Emden conjecture

The Lane–Emden system on `ℝⁿ` is `-Δu = v^p`, `-Δv = u^q`. The Lane–Emden conjecture asserts
that for `n ≥ 3`, `p, q > 0` and `1/(p+1) + 1/(q+1) > (n-2)/n` it has no positive classical
solution. Serrin and Zou proved the case `n = 3` for solutions of polynomial growth [SZ96],
Poláčik, Quittner and Souplet removed the growth condition [PQS07], and Souplet proved the case
`n = 4` [So09]. The weighted Hénon–Lane–Emden version `-Δu = |x|^A v^p`, `-Δv = |x|^B u^q`
appears as Conjecture C of Phan [Ph12] (for `A, B > -2`) and as Conjecture B of Huang and Zou
[HZ26] (for all real weights).

*References:*
- [HZ26] L.-H. Huang and W. Zou, *Liouville-type theorems for stable solutions of the
  Hénon–Lane–Emden system*, J. London Math. Soc. 113 (2026), e70412.
- [Ph12] Q. H. Phan, *Liouville-type theorems and bounds of solutions for Hardy–Hénon elliptic
  systems*, Adv. Differential Equations 17 (2012), 605–634.
- [PQS07] P. Poláčik, P. Quittner and P. Souplet, *Singularity and decay estimates in superlinear
  problems via Liouville-type theorems, I: Elliptic equations and systems*, Duke Math. J. 139
  (2007), 555–579.
- [So09] P. Souplet, *The proof of the Lane–Emden conjecture in four space dimensions*, Adv.
  Math. 221 (2009), 1409–1427.
- [SZ96] J. Serrin and H. Zou, *Non-existence of positive solutions of Lane–Emden systems*,
  Differential Integral Equations 9 (1996), 635–653.
- [OAI26] OpenAI, *The subcritical Hénon–Lane–Emden conjecture*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf
-/

@[expose] public section

open scoped Laplacian

namespace LaneEmdenConjecture

/-- Euclidean space `ℝⁿ`. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `(u, v)` is a positive classical solution of the Lane–Emden system `-Δu = v^p`,
`-Δv = u^q` on `ℝⁿ`. -/
structure IsLaneEmdenSolution (n : ℕ) (p q : ℝ) (u v : Space n → ℝ) : Prop where
  contDiff_u : ContDiff ℝ 2 u
  contDiff_v : ContDiff ℝ 2 v
  positive_u : ∀ x, 0 < u x
  positive_v : ∀ x, 0 < v x
  equation_u : ∀ x, -(Δ u) x = v x ^ p
  equation_v : ∀ x, -(Δ v) x = u x ^ q

/-- `(u, v)` is a positive solution of the Hénon–Lane–Emden system `-Δu = |x|^A v^p`,
`-Δv = |x|^B u^q` on `ℝⁿ \ {0}`, continuous on `ℝⁿ` and `C²` away from the origin. -/
structure IsHenonSolution (n : ℕ) (p q A B : ℝ) (u v : Space n → ℝ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  regular_u : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))
  regular_v : ContDiffOn ℝ 2 v ({0}ᶜ : Set (Space n))
  positive_u : ∀ x, 0 < u x
  positive_v : ∀ x, 0 < v x
  equation_u : ∀ x, x ≠ 0 → -(Δ u) x = ‖x‖ ^ A * v x ^ p
  equation_v : ∀ x, x ≠ 0 → -(Δ v) x = ‖x‖ ^ B * u x ^ q

/--
**The Lane–Emden conjecture.** For `n ≥ 3`, `p, q > 0` and `1/(p+1) + 1/(q+1) > (n-2)/n`, the
system `-Δu = v^p`, `-Δv = u^q` has no positive `C²` solution on `ℝⁿ`.

This was proved by an internal OpenAI model in September 2026 [OAI26], as a special case of the
weighted statement `lane_emden_conjecture.variants.henon`.
-/
@[category research solved, AMS 35]
theorem lane_emden_conjecture : ∀ n : ℕ, 3 ≤ n → ∀ p q : ℝ, 0 < p → 0 < q →
    1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n →
      ¬ ∃ u v, IsLaneEmdenSolution n p q u v := by
  sorry

/--
**The subcritical Hénon–Lane–Emden conjecture.** For `n ≥ 2`, `p, q > 0` and real `A, B` with
`(n+A)/(p+1) + (n+B)/(q+1) > n - 2`, the system `-Δu = |x|^A v^p`, `-Δv = |x|^B u^q` has no
positive solution that is continuous on `ℝⁿ` and `C²` away from the origin [Ph12, HZ26].

This was proved by an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 35]
theorem lane_emden_conjecture.variants.henon : ∀ n : ℕ, 2 ≤ n → ∀ p q A B : ℝ, 0 < p → 0 < q →
    ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - 2 →
      ¬ ∃ u v, IsHenonSolution n p q A B u v := by
  sorry

/-- **Serrin–Zou, Poláčik–Quittner–Souplet.** The Lane–Emden conjecture holds in dimension
three [SZ96, PQS07]. -/
@[category research solved, AMS 35]
theorem lane_emden_conjecture.variants.dim_three : ∀ p q : ℝ, 0 < p → 0 < q →
    1 / (p + 1) + 1 / (q + 1) > 1 / 3 → ¬ ∃ u v, IsLaneEmdenSolution 3 p q u v := by
  sorry

/-- **Souplet.** The Lane–Emden conjecture holds in dimension four [So09]. -/
@[category research solved, AMS 35]
theorem lane_emden_conjecture.variants.dim_four : ∀ p q : ℝ, 0 < p → 0 < q →
    1 / (p + 1) + 1 / (q + 1) > 1 / 2 → ¬ ∃ u v, IsLaneEmdenSolution 4 p q u v := by
  sorry

/-- The weighted statement with `A = B = 0` gives the Lane–Emden conjecture. -/
@[category test, AMS 35]
theorem lane_emden_of_henon (h : type_of% lane_emden_conjecture.variants.henon) :
    type_of% lane_emden_conjecture := by
  intro n hn p q hp hq hsub ⟨u, v, hs⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine h n (by omega) p q 0 0 hp hq ?_ ⟨u, v, ?_⟩
  · have key := mul_lt_mul_of_pos_left hsub hn'
    have e : (n : ℝ) * (((n : ℝ) - 2) / n) = n - 2 := by field_simp
    rw [e] at key
    calc (n : ℝ) - 2 < n * (1 / (p + 1) + 1 / (q + 1)) := key
      _ = ((n : ℝ) + 0) / (p + 1) + ((n : ℝ) + 0) / (q + 1) := by ring
  · exact
      { continuous_u := hs.contDiff_u.continuous
        continuous_v := hs.contDiff_v.continuous
        regular_u := hs.contDiff_u.contDiffOn
        regular_v := hs.contDiff_v.contDiffOn
        positive_u := hs.positive_u
        positive_v := hs.positive_v
        equation_u := fun x _ => by simp [hs.equation_u x]
        equation_v := fun x _ => by simp [hs.equation_v x] }

end LaneEmdenConjecture
