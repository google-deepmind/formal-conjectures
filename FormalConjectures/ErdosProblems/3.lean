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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 3

*References:*
- [erdosproblems.com/3](https://www.erdosproblems.com/3)
- [BlSi20] Bloom, Thomas F. and Sisask, Olof, *Breaking the logarithmic barrier in Roth's theorem
  on arithmetic progressions*. arXiv:2007.03528 (2020).
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Ge77] Gerver, Joseph L., *The sum of the reciprocals of a set of integers with no arithmetic
  progression of $k$ terms*. Proc. Amer. Math. Soc. (1977), 211-214.
- [Go01] Gowers, W. T., *A new proof of Szemerédi's theorem*. Geom. Funct. Anal. (2001), 465-588.
- [GrTa17] Green, Ben and Tao, Terence, *New bounds for Szemerédi's theorem, III: a
  polylogarithmic bound for $r_4(N)$*. Mathematika (2017).
- [KeMe23] Kelley, Zander and Meka, Raghu, *Strong bounds for 3-progressions*. 2023 IEEE 64th
  Annual Symposium on Foundations of Computer Science (FOCS) (2023).
- [LSS24] Leng, James, Sah, Ashwin and Sawhney, Mehtaab, *Improved bounds for Szemerédi's
  theorem*. arXiv:2402.17995 (2024).
- [OAI26] OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf
- [Pa07] Pal, Goutam, *On sequences of positive integers containing no $p$ terms in arithmetic
  progression*. arXiv:math/0703467 (2007).
- [TaVu06] Tao, Terence and Vu, Van, *Additive combinatorics*. Cambridge Studies in Advanced
  Mathematics 105 (2006).
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos3

set_option linter.style.formal_proof_palomar false in
/--
If $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?

Yes. This was proved by an internal OpenAI model in September 2026 [OAI26]; see the linked Lean
proof.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean#L38"]
theorem erdos_3 : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  sorry

/--
$r_k(N)$ is the largest size of a subset of $\{1, \dots, N\}$ that does not contain a non-trivial
$k$-term arithmetic progression.
-/
noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/--
There are $\beta > 0$ and $c > 0$ such that $r_3(N) \ll N \exp(-c (\log N)^{\beta})$.

Proved by Kelley and Meka [KeMe23].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.kelley_meka : ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (r 3 N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The case of $3$-term progressions: if $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$,
then $A$ contains a non-trivial $3$-term arithmetic progression.

Proved by Bloom and Sisask [BlSi20].
-/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/wilsonwu-ai/sundai-erdos-3/blob/8a58287a16558bf1e708eaa2d0f7cba4c86566a3/lean/Erdos3ThreeCase.lean#L96-L97"
    assuming erdos_3.variants.kelley_meka]
theorem erdos_3.variants.three : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength 3 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Fix $k \geq 3$. Every $A \subset \mathbb{N}$ with $\sum_{n \in A}\frac 1 n = \infty$ contains a
non-trivial $k$-term arithmetic progression if and only if the following holds: for every
$\varepsilon > 0$ there is $N$ such that every set $A$ of integers $\geq N$ with no non-trivial
$k$-term arithmetic progression has $\sum_{n \in A}\frac 1 n < \varepsilon$.

The second property, for every $k \geq 3$, is a question of Erdős [Er80, p. 92]. It is the last
question on [erdosproblems.com/169](https://www.erdosproblems.com/169). Pal [Pa07, Lemma 5] proved
that the first property implies the second at the same $k$. Gerver [Ge77] proved that the first
property for every $k$ is equivalent to a uniform bound on these sums for every $k$. The proof goes
through the convergence of $\sum_j r_k(4^j) / 4^j$, as in [TaVu06, Exercise 10.0.6].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/48826f608768cdc2bdab7c6996a30a34c70d453e/ErdosLean/Erdos169Er80.lean"]
theorem erdos_3.variants.uniform_tail_iff (k : ℕ) (hk : 3 ≤ k) :
    (∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength k) ↔
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree k → (∀ a ∈ A, N ≤ a) →
        (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For every $\varepsilon > 0$ there is $N$ such that every set $A$ of integers $\geq N$ with no
non-trivial $3$-term arithmetic progression has $\sum_{n \in A}\frac 1 n < \varepsilon$.

This is the case $k = 3$ of the question of Erdős [Er80] in `erdos_3.variants.uniform_tail_iff`.
It follows from the bound of Kelley and Meka [KeMe23], which makes $\sum_j r_3(4^j) / 4^j$
converge.
-/
@[category research solved, AMS 5 11,
  conditional formal_proof using lean4 at
    "https://github.com/mnn31/erdos-lean/blob/48826f608768cdc2bdab7c6996a30a34c70d453e/ErdosLean/Erdos169Er80.lean"
    assuming erdos_3.variants.kelley_meka]
theorem erdos_3.variants.uniform_tail_three :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree 3 → (∀ a ∈ A, N ≤ a) →
      (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For every $k \geq 3$ and $\varepsilon > 0$ there is $N$ such that every set $A$ of integers
$\geq N$ with no non-trivial $k$-term arithmetic progression has
$\sum_{n \in A}\frac 1 n < \varepsilon$.

This is the question of Erdős [Er80, p. 92] on
[erdosproblems.com/169](https://www.erdosproblems.com/169). By
`erdos_3.variants.uniform_tail_iff` it is equivalent to `erdos_3`, so it follows from `erdos_3`.
-/
@[category research solved, AMS 5 11,
  conditional formal_proof using lean4 at
    "https://github.com/mnn31/erdos-lean/blob/48826f608768cdc2bdab7c6996a30a34c70d453e/ErdosLean/Erdos169Er80.lean"
    assuming erdos_3]
theorem erdos_3.variants.uniform_tail :
    ∀ k : ℕ, 3 ≤ k → ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree k →
      (∀ a ∈ A, N ≤ a) → (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε := by
  sorry

/--
There is $c > 0$ such that $r_4(N) \ll N (\log N)^{-c}$.

Proved by Green and Tao [GrTa17].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.green_tao : ∃ c > (0 : ℝ),
    (fun N ↦ (r 4 N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.log N ^ (-c) := by
  sorry

/--
For every $k \geq 3$ there is $c_k > 0$ such that $r_k(N) \ll_k N (\log \log N)^{-c_k}$.

Proved by Gowers [Go01].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.gowers (k : ℕ) (hk : 3 ≤ k) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.log (Real.log N) ^ (-c) := by
  sorry

/--
For every $k \geq 5$ there is $c_k > 0$ such that $r_k(N) \ll_k N \exp(-(\log \log N)^{c_k})$.

Proved by Leng, Sah and Sawhney [LSS24].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.leng_sah_sawhney (k : ℕ) (hk : 5 ≤ k) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c) := by
  sorry

end Erdos3
