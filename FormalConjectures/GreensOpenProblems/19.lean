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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 19

*References:*
- [Gr26] [Ben Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.19)
- [FSS20] Fox, Jacob, et al. "Triforce and corners." Mathematical Proceedings of the Cambridge
  Philosophical Society. Vol. 169. No. 1. Cambridge University Press, 2020.
- [Ma21] Mandache, Matei. "A variant of the Corners theorem." Mathematical Proceedings of the
  Cambridge Philosophical Society. Vol. 171. No. 3. Cambridge University Press, 2021.
- [Ch11] Chu, Qing. "Multiple recurrence for two commuting transformations." Ergodic Theory and
  Dynamical Systems 31.3 (2011): 771-792.
-/

open Finset Real Classical

namespace Green19

section GroupDefs

-- Abstract representation to ease notation [FSS20].
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A corner in $A$ with common difference $d$ [FSS20]. -/
def IsCorner (A : Finset (G × G)) (x y d : G) : Prop :=
  (x, y) ∈ A ∧ (x + d, y) ∈ A ∧ (x, y + d) ∈ A

/--
From [FSS20]: given $A \subseteq G \times G$ and $d \in G$, let
$$S_d(A) = \lbrace (x, y) \in G \times G : (x, y), (x + d, y), (x, y + d) \in A \rbrace$$
-/
noncomputable def S (d : G) (A : Finset (G × G)) : Finset (G × G) :=
  univ.filter (fun p => IsCorner A p.1 p.2 d)

end GroupDefs

/-- The group $G = \mathbb{F}_2^n = (Z/2Z)^n$. -/
abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

/--
True if the given exponent satisfies Green's conditions [Gr26].
-/
def ValidExponent (c : ℝ) : Prop :=
  ∃ K > 0,
    ∀ α, 0 < α → α < 1 →
      ∀ᶠ n in Filter.atTop,
        ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
          let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
          (A.card : ℝ) ≥ α * N^2 →
          ∃ d : 𝔽₂ n, d ≠ 0 ∧ ((S d A).card : ℝ) ≥ K * α^c * N^2

/-- The infimum of all valid exponents [Gr26]. -/
noncomputable def C : ℝ := sInf {c | ValidExponent c}

/--
What is $C$, the infimum of all exponents $c$ for which the following is true, uniformly for
$0 < \alpha < 1$? Suppose that $A \subset \mathbb{F}_2^n \times \mathbb{F}_2^n$ is a set of density
$\alpha$. Write $N := 2^n$. Then there is some $d \neq 0$ such that $A$ contains $\gg \alpha^c N^2$
corners $(x,y), (x,y+d), (x+d,y)$.

This question has been resolved by [FSS20], showing that $C = 4$.
-/
@[category research solved, AMS 5 11]
theorem green_19 : C = 4 := by
  sorry

/-- [Ma21] showed that $3.13 \leq C$. -/
@[category research open, AMS 5 11]
theorem green_19.lower : C >= 3.13 := by
  sorry

/-- [Ma21] showed that $C \leq 4$. -/
@[category research open, AMS 5 11]
theorem green_19.upper : C <= 4 := by
  sorry

/- TODO(jeangud): in [FSS20] they mention that the corresponding question for squares
$(x, y), (x, y + d), (x + d, y), (x + d, y + d)$ is wide open (and here it is not even clear that
$C$ exists). -/

end Green19
