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

import FormalConjecturesUtil
import FormalConjectures.Wikipedia.LeopoldtConjecture
import FormalConjectures.Wikipedia.LeopoldtConjecture.All
import FormalConjecturesTest.LeopoldtCMProof.Equivalence

/-!
# Mihăilescu's Leopoldt conjecture agrees with every other formulation

`FormalConjecturesTest.LeopoldtCMProof.Equivalence` proves that Mihăilescu's Leopoldt defect
`Mihailescu.defect p K = ℤ-rk(E) - ℤ_p-rk(Ē)` vanishes exactly when the $\mathbb{Z}_p$-rank of
`closureE₁ K p` is $r_1 + r_2 - 1$, which is Wikipedia's form. Since
`FormalConjectures.Wikipedia.LeopoldtConjecture.All` already chains Wikipedia's form to the
other three, one composition puts Mihăilescu's statement into that list.

## Main results

* `Leopoldt.Mihailescu.leopoldtConjecture_tfae`: Mihăilescu's form, the elementary form, the
  triviality of every $p$-adic relation among units, the full rank of the matrix of $p$-adic
  logarithms, and the $\mathbb{Z}_p$-rank of $\overline{E_1}$ are all equivalent.
* `Leopoldt.Mihailescu.leopoldtConjecture_iff_padicRegulator_ne_zero`: for totally real `K`,
  Mihăilescu's form is Washington's $R_p(K) \neq 0$.

Note that none of this needs `p` odd, although [Mihăilescu, §1.1] assumes it: the equivalence
of the formulations is unconditional, and it is only the *proof* of the conjecture for CM fields
that uses oddness.
-/

open IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt.Mihailescu

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
**Mihăilescu's formulation joins the list.** For a number field `K` and a prime `p` the
following are equivalent: the Leopoldt defect `𝒟_L(K)` of [Mihăilescu, §1.1] vanishes; the
elementary congruence form; every $p$-adic relation among units of maximal rank in $E_1$ is
trivial; the matrix of $p$-adic logarithms has full rank; the $\mathbb{Z}_p$-rank of
$\overline{E_1}$ is $r_1 + r_2 - 1$.

The last four are `Leopoldt.leopoldtConjecture_tfae`; the first is tied to them by
`leopoldtConjecture_iff_finrank`.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_tfae :
    List.TFAE
      [LeopoldtConjecture p K,
       _root_.Leopoldt.LeopoldtConjecture K p,
       ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
         ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0,
       (logMatrix K p).rank = rank K,
       Module.finrank ℤ_[p] (closureE₁ K p) = rank K] := by
  tfae_have 1 ↔ 5 := leopoldtConjecture_iff_finrank K p
  tfae_have 5 ↔ 2 := zpRank_iff_leopoldtConjecture K p
  tfae_have 2 ↔ 3 := leopoldtConjecture_iff K p
  tfae_have 2 ↔ 4 := leopoldtConjecture_iff_rank K p
  tfae_finish

/--
For totally real `K`, Mihăilescu's Leopoldt defect vanishes exactly when Washington's $p$-adic
regulator $R_p(K)$ is nonzero. This is the form in which [Mihăilescu, Theorem 1] states the
conjecture ("the $p$-adic regulator of a number field does not vanish").
-/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    LeopoldtConjecture p K ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (leopoldtConjecture_iff_finrank K p).trans (zpRank_iff_padicRegulator_ne_zero K p σ₀ e)

end Leopoldt.Mihailescu
