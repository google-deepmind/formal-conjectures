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
# Erdős Problem 658

Is it true that if $A \subseteq \{1, \ldots, N\}^2$ has $|A| \geq \delta N^2$ then $A$ must
contain the vertices of a square? This is a problem of Graham if the square is restricted to be
axis-aligned; it is unclear whether in [Er97e] Erdős had this restriction in mind.

The axis-aligned case was proved via the density Hales–Jewett theorem by Furstenberg and
Katznelson [FuKa91], with a quantitative proof given by Solymosi [So04].

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_.
Proc. Int. Conf. on Discrete Math. (1997), 527-537.
[FuKa91] Furstenberg, H. and Katznelson, Y., _A density version of the Hales-Jewett theorem_.
J. Anal. Math. 57 (1991), 64–119.
[So04] Solymosi, J., _A Note on a Question of Erdős and Graham_.
Combin. Probab. Comput. 13 (2004), 263–267.

*Reference:* [erdosproblems.com/658](https://www.erdosproblems.com/658)
-/

open Finset

namespace Erdos658

/--
A subset $A$ of $\mathbb{N} \times \mathbb{N}$ contains the vertices of an axis-aligned square
if there exist $a, b, d$ with $d \geq 1$ such that all four corners
$(a, b)$, $(a + d, b)$, $(a, b + d)$, $(a + d, b + d)$ lie in $A$.
-/
def ContainsAxisAlignedSquare (A : Finset (ℕ × ℕ)) : Prop :=
  ∃ a b d : ℕ, d ≥ 1 ∧
    (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

/--
For any $\delta > 0$, for all sufficiently large $N$, if $A \subseteq \{1, \ldots, N\}^2$ has
$|A| \geq \delta N^2$ then $A$ must contain the vertices of an axis-aligned square.

This is a problem originally attributed to Graham [Er97e]. The qualitative statement
follows from the density Hales-Jewett theorem proved by Furstenberg and Katznelson [FuKa91].
A quantitative proof was given by Solymosi [So04].
-/
@[category research solved, AMS 5]
theorem erdos_658 : answer(True) ↔
    (∀ δ : ℝ, δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset (ℕ × ℕ),
          A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N →
          (A.card : ℝ) ≥ δ * (N : ℝ) ^ 2 →
          ContainsAxisAlignedSquare A) := by
  sorry

/--
A subset $A$ of $\mathbb{Z} \times \mathbb{Z}$ contains the vertices of a (possibly tilted)
square if there exist integers $a, b, d, e$ with $(d, e) \neq (0, 0)$ such that all four
vertices $(a, b)$, $(a+d, b+e)$, $(a+d-e, b+d+e)$, $(a-e, b+d)$ lie in $A$.
-/
def ContainsSquare (A : Finset (ℤ × ℤ)) : Prop :=
  ∃ a b d e : ℤ, (d ≠ 0 ∨ e ≠ 0) ∧
    (a, b) ∈ A ∧ (a + d, b + e) ∈ A ∧ (a + d - e, b + d + e) ∈ A ∧ (a - e, b + d) ∈ A

/--
General (tilted) square variant of Erdős Problem 658 [Er97e]: for any $\delta > 0$,
for all sufficiently large $N$, if $A \subseteq \{1, \ldots, N\}^2$ has $|A| \geq \delta N^2$
then $A$ must contain the vertices of a square (not necessarily axis-aligned).

It is unclear whether Erdős had the axis-aligned restriction in mind in [Er97e]. This variant
captures the more general interpretation where the square may be tilted.
-/
@[category research open, AMS 5]
theorem erdos_658_general : answer(sorry) ↔
    (∀ δ : ℝ, δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset (ℤ × ℤ),
          (∀ p ∈ A, (1 : ℤ) ≤ p.1 ∧ p.1 ≤ N ∧ (1 : ℤ) ≤ p.2 ∧ p.2 ≤ N) →
          (A.card : ℝ) ≥ δ * (N : ℝ) ^ 2 →
          ContainsSquare A) := by
  sorry

end Erdos658
