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
# Chollet's permanent conjecture

Oppenheim's inequality states that $\det(A \circ B) \ge \det(A) \det(B)$ for positive
semidefinite matrices $A$ and $B$, where $\circ$ is the Hadamard product. Chollet [Cho82]
conjectured the reverse inequality for the permanent.

The statements use the order `ComplexOrder` on $\mathbb{C}$. The permanents of $A$, $B$ and
$A \circ B$ are nonnegative real numbers, because $A \circ B$ is positive semidefinite by the
Schur product theorem.

*References:*
- [Cho82] J. Chollet, *Is there a permanental analogue to Oppenheim's inequality?*
  Amer. Math. Monthly 89 (1982), no. 1, 57–58.
  https://doi.org/10.1080/00029890.1982.11995380
- [GH87] R. J. Gregorac and I. R. Hentzel, *A note on the analogue of Oppenheim's inequality
  for permanents*. Linear Algebra Appl. 94 (1987), 109–112.
- [Rod24] K. Rodtes, *Chollet's permanent conjecture for $4 \times 4$ matrices*.
  Linear Multilinear Algebra 72 (2024), no. 16, 2633–2638.
  https://doi.org/10.1080/03081087.2023.2279150, [arXiv:2211.02839](https://arxiv.org/abs/2211.02839)
- [arXiv:1608.02844](https://arxiv.org/abs/1608.02844), F. Zhang,
  *An update on a few permanent conjectures*, Section 6.
-/

@[expose] public section

open scoped ComplexOrder Matrix

namespace CholletPermanent

variable {n : ℕ}

/--
**Chollet's permanent conjecture** [Cho82]: if $A$ and $B$ are Hermitian positive semidefinite
$n \times n$ complex matrices, then $\operatorname{per}(A \circ B) \le
\operatorname{per}(A) \operatorname{per}(B)$, where $\circ$ is the Hadamard product.
-/
@[category research open, AMS 15]
theorem chollet_permanent_conjecture (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).permanent ≤ A.permanent * B.permanent := by
  sorry

/--
The special case $B = \overline{A}$ of Chollet's conjecture: if $A$ is a Hermitian positive
semidefinite $n \times n$ complex matrix, then $\operatorname{per}(A \circ \overline{A}) \le
\operatorname{per}(A)^2$. Chollet [Cho82] showed that this case implies the full conjecture.
-/
@[category research open, AMS 15]
theorem chollet_permanent_conjecture.variants.conj (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) :
    (A ⊙ A.map star).permanent ≤ A.permanent ^ 2 := by
  sorry

/--
The real case of Chollet's conjecture [arXiv:1608.02844, Question 9]: if $A = (a_{ij})$ is a
real symmetric positive semidefinite $n \times n$ matrix, then
$\operatorname{per}(a_{ij}^2) \le \operatorname{per}(A)^2$.
-/
@[category research open, AMS 15]
theorem chollet_permanent_conjecture.variants.real (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) :
    (A ⊙ A).permanent ≤ A.permanent ^ 2 := by
  sorry

/--
Chollet's conjecture holds for $2 \times 2$ matrices [GH87].
-/
@[category research solved, AMS 15]
theorem chollet_permanent_conjecture.variants.two (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).permanent ≤ A.permanent * B.permanent := by
  sorry

/--
Chollet's conjecture holds for $3 \times 3$ matrices [GH87].
-/
@[category research solved, AMS 15]
theorem chollet_permanent_conjecture.variants.three (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).permanent ≤ A.permanent * B.permanent := by
  sorry

/--
Chollet's conjecture holds for $4 \times 4$ matrices [Rod24].
-/
@[category research solved, AMS 15]
theorem chollet_permanent_conjecture.variants.four (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).permanent ≤ A.permanent * B.permanent := by
  sorry

end CholletPermanent
