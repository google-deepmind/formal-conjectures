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
# Abhyankar–Sathaye embedding conjecture

*References:*
- [arxiv/2208.14736](https://arxiv.org/abs/2208.14736)
  **The Zariski Cancellation Problem and related problems in Affine Algebraic Geometry**
  by *Neena Gupta*
- [AM75] S. S. Abhyankar, T. T. Moh, *Embeddings of the line in the plane*,
  J. Reine Angew. Math. **276** (1975), 148–166.
- [Su74] M. Suzuki, *Propriétés topologiques des polynômes de deux variables complexes, et
  automorphismes algébriques de l'espace $\mathbb{C}^2$*, J. Math. Soc. Japan **26** (1974),
  241–257.
- [vdE00] A. van den Essen, *Polynomial Automorphisms and the Jacobian Conjecture*,
  Progress in Mathematics **190**, Birkhäuser, 2000.
-/

@[expose] public section

namespace Arxiv.«2208.14736»

open MvPolynomial

/--
A polynomial `f ∈ k[x_1, …, x_n]` is a *coordinate* if there exist
`f_2, …, f_n` such that `k[f, f_2, …, f_n] = k[x_1, …, x_n].`
-/
def IsCoordinate {k σ : Type*} [Field k] (f : MvPolynomial σ k) : Prop :=
  ∃ g : σ → MvPolynomial σ k, ∃ i : σ, g i = f ∧ Algebra.adjoin k (Set.range g) = ⊤

/--
Every variable is a coordinate.
-/
@[category test, AMS 13 14]
theorem isCoordinate_X
    {k σ : Type*} [Field k] (i : σ) : IsCoordinate (X i : MvPolynomial σ k) := by
  unfold IsCoordinate
  use X, i
  constructor
  · rfl
  · exact adjoin_range_X

/--
The **Abhyankar–Sathaye embedding conjecture**: let `k` be a field of characteristic `0`
and `n ≥ 3`. If `f ∈ k[x_1, …, x_n]` is such that `k[x_1, …, x_n] / (f) ≅ k[y_1, …, y_{n-1}]`
as `k`-algebras, then `f` is a coordinate of `k[x_1, …, x_n]`.

Geometrically: every closed embedding of $\mathbb{A}^{n-1}$ into $\mathbb{A}^n$ as a hypersurface
is rectifiable. The conjecture is open for every `n ≥ 3`, even for `k = ℂ`.
See [arxiv/2208.14736] and [vdE00].
-/
@[category research open, AMS 13 14]
theorem abhyankar_sathaye
    (n : ℕ) (hn : n ≥ 3) {k : Type*} [Field k] [CharZero k] (f : MvPolynomial (Fin n) k)
    (h : Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span {f}) ≃ₐ[k] MvPolynomial (Fin (n - 1)) k)) :
    IsCoordinate f := by
  sorry

/--
The case `n = 2` of the embedding conjecture is the **Abhyankar–Moh–Suzuki theorem**:
over a field of characteristic `0`, every `f ∈ k[x, y]` with `k[x, y] / (f) ≅ k[t]`
is a coordinate. See [AM75] and [Su74].
-/
@[category research solved, AMS 13 14]
theorem abhyankar_sathaye.variants.dim_two
    {k : Type*} [Field k] [CharZero k] (f : MvPolynomial (Fin 2) k)
    (h : Nonempty ((MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) ≃ₐ[k] MvPolynomial (Fin 1) k)) :
    IsCoordinate f := by
  sorry

end Arxiv.«2208.14736»
