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
# Remarks on the disproof of the unit distance conjecture

*Reference:* [arxiv/2605.20695](https://arxiv.org/abs/2605.20695)
**Remarks on the disproof of the unit distance conjecture**
by *N. Alon, T. F. Bloom, W. T. Gowers, D. Litt, W. Sawin, A. Shankar, J. Tsimerman, V. Wang,
and M. Matchett Wood* (2026).

A short, human-verified digest of the OpenAI-generated disproof of Erdős's unit distance
conjecture (see `FormalConjectures.ErdosProblems.«90»`). The main theorem of the paper is
the qualitative form recorded in
`Erdos90.erdos_90.variants.polynomial_lower_bound`; this file records the load-bearing
arithmetic input — the existence of an infinite tower of totally real fields with bounded root
discriminant and infinitely many completely split primes `q ≡ 1 (mod 4)` (Proposition 2.3).
-/

open NumberField

namespace Arxiv.«2605.20695»

/--
**Proposition 2.3 (Remarks on the disproof of the unit distance conjecture, 2026).**

There exists an infinite tower of totally real number fields `F / ℚ` with *uniformly* bounded
root discriminant `|disc F|^{1/[F:ℚ]} ≤ rdBound`, such that for each field in the tower the
set of rational primes `q ≡ 1 (mod 4)` that split completely in `F` is infinite.

The existence of this tower is the key arithmetic input to the disproof of Erdős's unit
distance conjecture (Erdős problem #90). It is proved in the Remarks paper via the
Hajir–Maire–Ramakrishna (2003) construction, which in turn applies the Golod–Shafarevich
inequality to a controlled pro-`2` Galois group.

A "completely split" rational prime `q` in `F` is one for which `(q : 𝓞 F)` is the product of
exactly `[F:ℚ]` distinct maximal ideals (equivalently, both the ramification index and the
residue degree of every prime above `q` are `1`).
-/
@[category research solved, AMS 11]
theorem prop_2_3_totally_real_tower :
    ∃ (rdBound : ℝ),
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        {q : ℕ | q.Prime ∧ q % 4 = 1 ∧
          ∃ (factors : Finset (Ideal (𝓞 F))),
            factors.card = Module.finrank ℚ F ∧
            ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p}.Infinite := by
  sorry

end Arxiv.«2605.20695»
