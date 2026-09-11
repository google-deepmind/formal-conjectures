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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Minimal discriminants of elliptic curves over number fields

The minimal discriminant ideal of an elliptic curve over a number field, together with the
local exponents cutting it out.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Section VIII.8.
-/

@[expose] public section

namespace WeierstrassCurve

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The exponent of `v` in the minimal discriminant ideal of `W`: the normalized additive
valuation of the discriminant of a minimal model over the `v`-adic integers.
A vanishing discriminant has valuation `⊤`, which `toNat` sends to `0`, so this is only
meaningful for elliptic `W`. -/
noncomputable def minimalDiscriminantExponent (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (IsDiscreteValuationRing.addVal (v.adicCompletionIntegers K)
    (((W⁄(v.adicCompletion K)).minimal (v.adicCompletionIntegers K)).integralModel
      (v.adicCompletionIntegers K)).Δ).toNat

/-- The minimal discriminant ideal of an elliptic curve over a number field is the product of
the local minimal discriminant ideals `v.asIdeal ^ W.minimalDiscriminantExponent v` over
all nonzero prime ideals `v` of its ring of integers. Only finitely many exponents are nonzero.
See [LMFDB](https://www.lmfdb.org/knowledge/show/ec.minimal_discriminant). -/
noncomputable def minimalDiscriminantIdeal (W : WeierstrassCurve K) [W.IsElliptic] :
    Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ W.minimalDiscriminantExponent v

end WeierstrassCurve
