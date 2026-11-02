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
# Falconer's distance set conjecture

If $d \ge 2$ and $E \subseteq \mathbb{R}^d$ is compact with $\dim_H E > \frac{d}{2}$, then the
distance set
$$\{ |x - y| \mid x, y \in E \}$$
has positive Lebesgue measure. The restriction $d \ge 2$ is needed; see `falconer_conjecture`.

## References

* [K. Falconer, *On the Hausdorff dimensions of distance sets*](https://doi.org/10.1112/S0025579300010998)
* [Wikipedia, *Falconer's conjecture*](https://en.wikipedia.org/wiki/Falconer%27s_conjecture)
* [OAI26a] OpenAI, *The Falconer distance conjecture in all dimensions*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf
-/

@[expose] public section

namespace Falconer

open MeasureTheory Set

open scoped ENNReal EuclideanGeometry

set_option linter.style.formal_proof_palomar false in
/-- Falconer's distance set conjecture, $d = 2$ case.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. The linked statement is `falconer_conjecture_two.variants.main_target`; see
`falconer_conjecture_two_of_main_target`. -/
@[category research solved, AMS 28 42, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Main.lean#L50"]
lemma falconer_conjecture_two (E : Set <| ℝ²) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    0 < volume (image2 dist E E) := sorry

set_option linter.style.formal_proof_palomar false in
/-- Falconer's distance set conjecture in dimension $d \ge 2$.

The hypothesis $2 \le d$ excludes a degenerate case: the conclusion is false for $d = 1$.
The base-$7$ Cantor set $E = \{\sum_{n \ge 1} a_n 7^{-n} : a_n \in \{0, 1, 2\}\}$ is compact
with $\dim_H E = \log 3 / \log 7 > 1/2$, but $E - E$ has digits in $\{-2, \dots, 2\}$, so
after fixing $n$ digits it is covered by $5^n$ intervals of length $\frac{2}{3} 7^{-n}$ and is
therefore null; its distance set is the image of $E - E$ under $|\cdot|$ and is null too.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. The linked statement is `falconer_conjecture.variants.all_dimensions`; see
`falconer_conjecture_of_all_dimensions`. -/
@[category research solved, AMS 28 42, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Campaign123PlanarFurstenbergProof.lean#L47"]
lemma falconer_conjecture (d : ℕ) (h2d : 2 ≤ d) (E : Set <| ℝ^d) (hc : IsCompact E)
    (hd : d < 2 * dimH E) :
    0 < volume (image2 dist E E) := sorry

set_option linter.style.formal_proof_palomar false in
/-- The statement of the linked Lean proof of `falconer_conjecture_two`, with its definitions
unfolded: the hypothesis is $\dim_H E > 1$ and the distance set is written out. -/
@[category research solved, AMS 28 42, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Main.lean#L50"]
theorem falconer_conjecture_two.variants.main_target :
    ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E → 1 < dimH E →
      0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The statement of the linked Lean proof of `falconer_conjecture`: the hypothesis is
$\dim_H E > d / 2$ and the distance set is written out. -/
@[category research solved, AMS 28 42, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Campaign123PlanarFurstenbergProof.lean#L47"]
theorem falconer_conjecture.variants.all_dimensions :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
  sorry

/-- `2 < 2 * dimH E` gives `1 < dimH E`, and `image2 dist E E` is the distance set. -/
@[category test, AMS 28 42]
theorem falconer_conjecture_two_of_main_target
    (h : type_of% falconer_conjecture_two.variants.main_target) :
    type_of% falconer_conjecture_two := by
  intro E hc hd
  refine h E hc ?_
  by_contra hle
  have : 2 * dimH E ≤ 2 * 1 := by
    gcongr
    exact not_lt.mp hle
  rw [mul_one] at this
  exact absurd hd (not_lt.mpr this)

/-- `d < 2 * dimH E` is `d / 2 < dimH E` in `ℝ≥0∞`, and `image2 dist E E` is the distance set. -/
@[category test, AMS 28 42]
theorem falconer_conjecture_of_all_dimensions
    (h : type_of% falconer_conjecture.variants.all_dimensions) :
    type_of% falconer_conjecture := by
  intro d h2d E hc hd
  refine h d h2d E hc ?_
  rw [ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_comm]
  exact hd

end Falconer
