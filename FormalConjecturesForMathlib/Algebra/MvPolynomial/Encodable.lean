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

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Logic.Denumerable

public section

/-!
# `Encodable` and `Denumerable` instances for multivariate polynomials

`MvPolynomial σ R` is `AddMonoidAlgebra R (σ →₀ ℕ)`, so a polynomial is determined by its
finitely supported family of coefficients. Transporting the `Encodable (α →₀ β)` instance
along `AddMonoidAlgebra.coeffEquiv` therefore encodes the polynomials over an encodable
coefficient ring in an encodable set of variables.

In particular `MvPolynomial ℕ ℤ` is `Denumerable`, and hence `Primcodable` through
`Primcodable.ofDenumerable`, so it makes sense to ask whether a predicate on integer
polynomials in countably many variables is decidable by an algorithm. This is what
Hilbert's 10th problem asks; see `FormalConjectures/HilbertProblems/10.lean`.
-/

namespace MvPolynomial

instance instEncodable {σ R : Type*} [CommSemiring R] [Encodable σ] [Encodable R]
    [∀ x : R, Decidable (x ≠ 0)] : Encodable (MvPolynomial σ R) :=
  .ofEquiv _ AddMonoidAlgebra.coeffEquiv

instance instDenumerable : Denumerable (MvPolynomial ℕ ℤ) := .ofEncodableOfInfinite _

end MvPolynomial
