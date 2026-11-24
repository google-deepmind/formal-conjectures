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
# Ben Green's Open Problem 73

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.73)
- [Th69] Thom, R., *Sur les variétés d'ordre fini*. Global Analysis (Papers in Honor of K. Kodaira),
  Univ. Tokyo Press, Tokyo (1969), 397-401.
- [CM09] Chaperon, M. and Meyer, D., *On a theorem of René Thom in "géométrie finie"*.
  Enseign. Math. (2) 55 (2009), no. 3-4, 329-357.
  [doi:10.5169/seals-110107](https://doi.org/10.5169/seals-110107)
- [DL12] Dvir, Z. and Lovett, S., *Subspace evasive sets*. STOC '12, ACM (2012), 351-358.
  [arXiv:1110.5696](https://arxiv.org/abs/1110.5696)
-/

@[expose] public section

open ContDiff Set

namespace Green73

/-- The ambient space $\mathbb{R}^{m+2} = \mathbb{R}^m \times \mathbb{R}^2$. -/
abbrev Ambient (m : ℕ) : Type := (Fin m → ℝ) × (Fin 2 → ℝ)

/-- The open cube $(-r, r)^m \subset \mathbb{R}^m$. -/
def cube (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  Set.pi univ fun _ ↦ Ioo (-r) r

/--
The local piece $\Gamma = \{(x, f(x)) : x \in (-1, 1)^m\}$ of the codimension $2$ surface given by
the graph of `f`, as a subset of $\mathbb{R}^m \times \mathbb{R}^2$.
-/
def graphPiece {m : ℕ} (f : (Fin m → ℝ) → (Fin 2 → ℝ)) : Set (Ambient m) :=
  {p | p.1 ∈ cube m 1 ∧ p.2 = f p.1}

/--
Let $\Gamma$ be a smooth codimension 2 surface in $\mathbb{R}^n$. Must $\Gamma$ intersect some
2-dimensional plane in 5 points, if $n$ is sufficiently large?

[Gr24] intends the question to be local: "for the purposes of this problem one can take
$\Gamma = \{(x, f(x)) : x \in (-1, 1)^{n-2}\}$ for some smooth function
$f : (-2, 2)^{n-2} \to \mathbb{R}^2$ with $f(0) = 0$, say." We state this local form, with
$m = n - 2$ and $n = m + 2$. "Smooth" is `ContDiffOn ℝ ∞` on the open cube, a "2-dimensional
plane" is an affine subspace whose direction has dimension $2$, and "in $5$ points" is read as
"in at least $5$ points" (the intersection may be infinite, `encard = ⊤`).

[Gr24] remarks that the analogous number of intersection points for codimension $d$ and
$d$-dimensional planes is finite (sketched by Thom [Th69], with details in [CM09] and explicit
constructions in [DL12]), and that it is not known whether it is bounded independently of $n$ for
$d = 2$.
-/
@[category research open, question, AMS 53 57]
theorem green_73 :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ f : (Fin m → ℝ) → (Fin 2 → ℝ),
      ContDiffOn ℝ ∞ f (cube m 2) → f 0 = 0 →
        ∃ P : AffineSubspace ℝ (Ambient m), Module.finrank ℝ P.direction = 2 ∧
          5 ≤ (graphPiece f ∩ (P : Set (Ambient m))).encard := by
  sorry

end Green73
