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
*Reference:* J. Chollet,
[Is there a permanental analogue to Oppenheim's inequality?](https://doi.org/10.1080/00029890.1982.11995380),
Amer. Math. Monthly 89 (1982), 57–58.
-/

@[expose] public section

open ComplexOrder

namespace CholletConjecture

/-- Chollet's conjecture: For every $n \in \mathbb{N}$ (the case $n = 0$ is trivial),
for every Hermitian positive semidefinite $A, B \in \mathbb{C}^{n \times n}$,
$$
\operatorname{per}(A \circ B) \leq \operatorname{per}(A) \cdot \operatorname{per}(B)
$$
where $\circ$ is the Hadamard product.

[Ch82] Chollet, J., Is there a permanental analogue to Oppenheim's inequality?
Amer. Math. Monthly 89 (1982), 57–58.
-/
@[category research open, AMS 15]
theorem chollet_conjecture (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

/-- Chollet's conjecture holds for $n \le 3$.

[GH87](https://doi.org/10.1016/0024-3795%2887%2990082-6) R. J. Gregorac, I. R. Hentzel,
A note on the analogue of Oppenheim's inequality for permanents,
Linear Algebra Appl. 94 (1987), 109–112.
-/
@[category research solved, AMS 15]
theorem chollet_conjecture.variants.le_three (n : ℕ)
    (hn : n ≤ 3)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

/-- Chollet's conjecture holds for $4 \times 4$ real matrices.

[Hu21](https://doi.org/10.1515/spma-2020-0126) G. Hutchinson,
An elementary proof of Chollet's permanent conjecture for 4 × 4 real matrices,
Special Matrices 9 (2021), 83–102.
-/
@[category research solved, AMS 15]
theorem chollet_conjecture.variants.real.four (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

/-- Chollet's conjecture holds for $4 \times 4$ matrices.

[Ro24](https://doi.org/10.1080/03081087.2023.2279150) K. Rodtes,
Chollet's permanent conjecture for 4 × 4 matrices,
Linear Multilinear Algebra 72(16) (2024), 2633–2638.
-/
@[category research solved, AMS 15]
theorem chollet_conjecture.variants.four (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

end CholletConjecture
