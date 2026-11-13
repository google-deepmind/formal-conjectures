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
# Ehrhart's volume conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Ehrhart%27s_volume_conjecture)
- [Ehr55] Ehrhart, E., *Une généralisation du théorème de Minkowski*.
  C. R. Acad. Sci. Paris 240 (1955), 483-485.
- [Ehr64] Ehrhart, E., *Une généralisation probable du théorème fondamental de Minkowski*.
  C. R. Acad. Sci. Paris 258 (1964), 4885-4887.
- [Ehr79] Ehrhart, E., *Volume réticulaire critique d'un simplexe*.
  J. Reine Angew. Math. 305 (1979), 218-220.
- [NP14] Nill, B. and Paffenholz, A., *On the equality case in Ehrhart's volume conjecture*.
  Adv. Geom. 14 (2014), 579-586. [arXiv:1205.1270](https://arxiv.org/abs/1205.1270)
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science* (2026),
  Chapter 8. [PDF](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
-/

@[expose] public section

open MeasureTheory

namespace EhrhartVolumeConjecture

/--
A convex body $K \subseteq \mathbb{R}^n$ whose barycenter is the origin and whose only interior
lattice point is the origin. The barycenter is Mathlib's set average
$\frac{1}{\mathrm{vol}(K)} \int_K x \, dx$ with respect to Lebesgue measure.
-/
structure IsEhrhartBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  isCompact : IsCompact K
  interior_nonempty : (interior K).Nonempty
  barycenter_eq_zero : ⨍ x in K, x = 0
  interior_lattice_points : {z : Fin n → ℤ | (fun i ↦ (z i : ℝ)) ∈ interior K} = {0}

/--
The simplex $(n+1)\Delta_n - (1, \dots, 1)$, where $\Delta_n = \mathrm{conv}\{0, e_1, \dots, e_n\}$.
Its vertices are $(-1, \dots, -1)$ and $(n+1)e_j - (1, \dots, 1)$ for $j = 1, \dots, n$.
-/
def centeredSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, -1 ≤ x i) ∧ ∑ i, x i ≤ 1}

@[category test, AMS 52]
theorem zero_mem_centeredSimplex (n : ℕ) : 0 ∈ centeredSimplex n := by
  simp [centeredSimplex]

@[category test, AMS 52]
theorem neg_one_mem_centeredSimplex (n : ℕ) : (fun _ ↦ -1) ∈ centeredSimplex n := by
  simp [centeredSimplex]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

@[category test, AMS 52]
theorem vertex_mem_centeredSimplex (n : ℕ) (j : Fin n) :
    (fun i ↦ (n + 1 : ℝ) * (if i = j then 1 else 0) - 1) ∈ centeredSimplex n := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · dsimp only
    split_ifs <;> linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · simp [Finset.sum_sub_distrib]

set_option linter.style.formal_proof_palomar false in
/--
Let $K \subseteq \mathbb{R}^n$ be a convex body whose barycenter is its only interior lattice
point. Then
$$\mathrm{vol}(K) \le \frac{(n+1)^n}{n!}.$$

Ehrhart [Ehr64] proposed this bound. He proved it for $n = 2$ [Ehr55] and for simplices
[Ehr79]. OpenAI
[OpenAI26, Theorem 1.1] proved it in every dimension, with a Lean proof of this statement.
After an integer translation the barycenter can be taken to be the origin.
-/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/EhrhartVolumeInequality.lean#L55733-L55749"]
theorem ehrhart_volume_conjecture {n : ℕ} (hn : 0 < n) {K : Set (Fin n → ℝ)}
    (hK : IsEhrhartBody K) :
    volume.real K ≤ (n + 1) ^ n / n.factorial := by
  sorry

/--
The bound in `ehrhart_volume_conjecture` is attained by `centeredSimplex n`.
-/
@[category textbook, AMS 11 52]
theorem ehrhart_volume_conjecture.variants.sharp {n : ℕ} (hn : 0 < n) :
    IsEhrhartBody (centeredSimplex n) ∧
      volume.real (centeredSimplex n) = (n + 1) ^ n / n.factorial := by
  sorry

/--
The equality case: if equality holds in `ehrhart_volume_conjecture`, then $K$ is the image of
`centeredSimplex n` under an integer linear map of determinant $\pm 1$ [NP14, Conjecture 1.1].
Ehrhart proved this for $n = 2$ (see [NP14, Section 1]), and Nill and Paffenholz
[NP14, Theorem 1.4] proved it for convex bodies contained in the dual of a lattice polytope.
[OpenAI26] does not determine the equality cases.
-/
@[category research open, AMS 11 52]
theorem ehrhart_volume_conjecture.variants.equality {n : ℕ} (hn : 0 < n)
    {K : Set (Fin n → ℝ)} (hK : IsEhrhartBody K)
    (hvol : volume.real K = (n + 1) ^ n / n.factorial) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, IsUnit A.det ∧
      K = (fun x ↦ (A.map (↑) : Matrix (Fin n) (Fin n) ℝ).mulVec x) '' centeredSimplex n := by
  sorry

end EhrhartVolumeConjecture
