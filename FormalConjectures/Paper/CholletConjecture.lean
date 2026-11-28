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

*References:*
* [Ch82] Chollet, J. (1982). "Is there a permanental analogue to Oppenheim's inequality?"
  *Amer. Math. Monthly* 89, pp. 57--58.
  [doi:10.1080/00029890.1982.11995380](https://doi.org/10.1080/00029890.1982.11995380)
* [GH87] Gregorac, R. J. and Hentzel, I. R. (1987). "A note on the analogue of Oppenheim's
  inequality for permanents." *Linear Algebra Appl.* 94, pp. 109--112.
  [doi:10.1016/0024-3795(87)90082-6](https://doi.org/10.1016/0024-3795%2887%2990082-6)
* [Hu21] Hutchinson, G. (2021). "An elementary proof of Chollet's permanent conjecture
  for 4 × 4 real matrices." *Special Matrices* 9, pp. 83--102.
  [doi:10.1515/spma-2020-0126](https://doi.org/10.1515/spma-2020-0126)
* [Ro24] Rodtes, K. (2024). "Chollet's permanent conjecture for 4 × 4 matrices."
  *Linear Multilinear Algebra* 72(16), pp. 2633--2638.
  [doi:10.1080/03081087.2023.2279150](https://doi.org/10.1080/03081087.2023.2279150)
-/

@[expose] public section

open ComplexOrder

namespace CholletConjecture

/-- Chollet's conjecture: For every $n \in \mathbb{N}$,
for every Hermitian positive semidefinite $A, B \in \mathbb{C}^{n \times n}$,
$$
\operatorname{per}(A \circ B) \leq \operatorname{per}(A) \cdot \operatorname{per}(B)
$$
where $\circ$ is the Hadamard product [Ch82].
-/
@[category research open, AMS 15]
theorem chollet_conjecture (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

/-- Chollet's conjecture holds for $n \le 4$.

Proved for $n \le 3$ in [GH87] and for $n = 4$ in [Ro24].
-/
@[category research solved, AMS 15]
theorem chollet_conjecture.variants.le_four (n : ℕ)
    (hn : n ≤ 4)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

/-- Chollet's conjecture for real matrices.

For $n = 4$, this was first proved in [Hu21].
-/
@[category research open, AMS 15]
theorem chollet_conjecture.variants.real (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hApos : A.PosSemidef) (hBpos : B.PosSemidef) :
    (A.hadamard B).permanent ≤ A.permanent * B.permanent := by
  sorry

end CholletConjecture
