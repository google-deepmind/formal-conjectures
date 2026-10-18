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
# A Cauchy–Schwarz inequality for real powers

For a vector $v$ and a real number $p$, write $v^p$ for the entrywise power of $v$. Johnston,
Plosker, Torrance and Varona proved that
$\|v^p\| \|w^p\| - \langle v^p, w^p \rangle \le \|v\|^p \|w\|^p - \langle v, w \rangle^p$
for every positive integer $p$, showed that it fails for $1 < p < 2$, and conjectured that it holds
for all positive vectors and every real $p \ge 2$.

*References:*
- [JPTV25] [arxiv/2507.10327](https://arxiv.org/abs/2507.10327)
  **Generalizing the Cauchy–Schwarz inequality: Hadamard powers and tensor products**
  by *Nathaniel Johnston, Sarah Plosker, Charles Torrance, Luis M. B. Varona*,
  Linear Multilinear Algebra (2026), Conjecture 5.1.
- [JS26] [arxiv/2610.12063](https://arxiv.org/abs/2610.12063)
  **Hadamard powers of Gram matrices and Generalized Cauchy-Schwarz inequalities**
  by *Nathaniel Johnston, Mohammad Sababheh*.
- [Ga26] [doi/10.5281/zenodo.23237507](https://doi.org/10.5281/zenodo.23237507)
  **A Cauchy–Schwarz inequality for real powers: proof, equality cases and weighted forms**
  by *Pragyaan Gaur*.
-/

@[expose] public section

namespace Arxiv.«2507.10327»

/-- The entrywise real power $v^p$ of a vector $v \in \mathbb{R}^n$. -/
noncomputable def epow {n : ℕ} (p : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ v i ^ p

@[category test, AMS 15]
theorem epow_apply {n : ℕ} (p : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    epow p v i = v i ^ p := rfl

/--
Let $p \ge 2$ be a real number. For all vectors $v, w \in \mathbb{R}^n$ with positive entries,
$\|v^p\| \|w^p\| - \langle v^p, w^p \rangle \le \|v\|^p \|w\|^p - \langle v, w \rangle^p$.

This was proved independently by Johnston and Sababheh [JS26] and by Gaur [Ga26]. The linked
Lean proof assumes only nonnegative entries.
-/
@[category research solved, AMS 15 26, formal_proof using lean4 at
  "https://github.com/pragyaangaur/Real-Power-Cauchy-Schwarz/blob/ae6dbb4ba8ca832a42e2281f713374b8e0f1dc49/RealPowerCauchySchwarz/Basic.lean#L384"]
theorem conjecture_5_1 {n : ℕ} (p : ℝ) (hp : 2 ≤ p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) ≤
      ‖v‖ ^ p * ‖w‖ ^ p - inner ℝ v w ^ p := by
  sorry

/--
The case of a positive integer $p$ holds for all real vectors $v, w \in \mathbb{R}^n$:
$\|v^p\| \|w^p\| - |\langle v^p, w^p \rangle| \le \|v\|^p \|w\|^p - |\langle v, w \rangle|^p$
([JPTV25], Corollary 3.4).
-/
@[category research solved, AMS 15 26]
theorem conjecture_5_1.variants.nat {n : ℕ} (p : ℕ) (hp : 1 ≤ p)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ‖epow p v‖ * ‖epow p w‖ - |inner ℝ (epow p v) (epow p w)| ≤
      ‖v‖ ^ p * ‖w‖ ^ p - |inner ℝ v w| ^ p := by
  sorry

/--
The bound $p \ge 2$ cannot be lowered to $p > 1$: for every $p \in (1, 2)$ there are positive
vectors $v, w \in \mathbb{R}^2$ for which the inequality fails ([JPTV25], Example 1).
-/
@[category research solved, AMS 15 26]
theorem conjecture_5_1.variants.one_lt_two (p : ℝ) (hp : p ∈ Set.Ioo 1 2) :
    ∃ v w : EuclideanSpace ℝ (Fin 2), (∀ i, 0 < v i) ∧ (∀ i, 0 < w i) ∧
      ‖v‖ ^ p * ‖w‖ ^ p - inner ℝ v w ^ p <
        ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) := by
  sorry

end Arxiv.«2507.10327»
