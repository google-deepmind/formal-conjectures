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
import FormalConjectures.Wikipedia.LeopoldtConjecture.Elementary
import FormalConjectures.Wikipedia.LeopoldtConjecture.PadicRegulator
import FormalConjectures.Wikipedia.LeopoldtConjecture.Regulator
import FormalConjectures.Wikipedia.LeopoldtConjecture.ZpRank

/-!
# All formulations of Leopoldt's conjecture agree

Each equivalence is proved in its own file; this file collects them, so every proof below is a
single line. `leopoldtConjecture_tfae` is the summary: for a number field `K` and a prime `p`,
the following are equivalent.

1. `LeopoldtConjecture K p` — the elementary form: congruences modulo $p^M \mathcal{O}_K$ force
   divisibility of the exponents.
2. Every $p$-adic relation among units of maximal rank lying in $E_1$ is trivial. This is the
   conclusion of `Leopoldt.leopoldt_conjecture`.
3. `(logMatrix K p).rank = rank K` — the matrix of $p$-adic logarithms has full rank. This is
   `Leopoldt.leopoldt_conjecture.variants.padicRegulator`.
4. `Module.finrank ℤ_[p] (closureE₁ K p) = rank K` — Wikipedia's $\mathbb{Z}_p$-rank form. This
   is `Leopoldt.leopoldt_conjecture.variants.zpRank`.

For totally real `K` a fifth is `padicRegulator K p σ₀ e ≠ 0`, Washington's $R_p(K) \neq 0$,
which is `leopoldtConjecture_iff_padicRegulator_ne_zero` and cannot join the list above because
it needs the extra hypothesis and the choice of a deleted embedding.

Where each equivalence is proved:

| Equivalence | File |
| --- | --- |
| (1) ↔ (2) | `LeopoldtConjecture.Elementary` |
| (1) ↔ (3), (2) ↔ (3) | `LeopoldtConjecture.PadicRegulator` |
| (4) ↔ (2) | `LeopoldtConjecture.ZpRank` |
| (1) ↔ $R_p \neq 0$ | `LeopoldtConjecture.Regulator` |
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- The $\mathbb{Z}_p$-rank form and the elementary form agree. -/
@[category API, AMS 11]
theorem zpRank_iff_leopoldtConjecture :
    Module.finrank ℤ_[p] (closureE₁ K p) = rank K ↔ LeopoldtConjecture K p :=
  (zpRank_iff K p).trans (leopoldtConjecture_iff K p).symm

/-- The $\mathbb{Z}_p$-rank form and the full-rank form of the $p$-adic regulator agree. -/
@[category API, AMS 11]
theorem zpRank_iff_rank :
    Module.finrank ℤ_[p] (closureE₁ K p) = rank K ↔ (logMatrix K p).rank = rank K :=
  (zpRank_iff K p).trans (forall_isPadicRelation_iff_rank K p)

/-- For totally real `K`, the $\mathbb{Z}_p$-rank form and $R_p(K) \neq 0$ agree. -/
@[category API, AMS 11]
theorem zpRank_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    Module.finrank ℤ_[p] (closureE₁ K p) = rank K ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (zpRank_iff_leopoldtConjecture K p).trans (leopoldtConjecture_iff_padicRegulator_ne_zero K p σ₀ e)

/--
**All four formulations of Leopoldt's conjecture are equivalent**: the elementary form, the
triviality of every $p$-adic relation among units, the full rank of the matrix of $p$-adic
logarithms, and Wikipedia's $\mathbb{Z}_p$-rank of the closure of $E_1$.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_tfae :
    List.TFAE
      [LeopoldtConjecture K p,
       ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
         ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0,
       (logMatrix K p).rank = rank K,
       Module.finrank ℤ_[p] (closureE₁ K p) = rank K] := by
  tfae_have 1 ↔ 2 := leopoldtConjecture_iff K p
  tfae_have 1 ↔ 3 := leopoldtConjecture_iff_rank K p
  tfae_have 4 ↔ 1 := zpRank_iff_leopoldtConjecture K p
  tfae_finish

end Leopoldt
