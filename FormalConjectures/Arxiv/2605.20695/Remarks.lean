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

There exist `rdBound : ℝ` and a *single* infinite set `Q` of rational primes `q ≡ 1 (mod 4)`
such that for every `N : ℕ` one can find a totally real number field `F / ℚ` of degree `≥ N`
with uniformly bounded root discriminant `|disc F|^{1/[F:ℚ]} ≤ rdBound` in which every prime
`q ∈ Q` splits completely.

As in `Arxiv.«2605.20579».lemmas_11_12_tower`, the load-bearing feature is that `Q` is fixed
*before* `F`: the same primes split completely in fields of *unbounded* degree. (For a single
fixed `F`, Chebotarev already supplies infinitely many completely split primes `≡ 1 (mod 4)`,
so a per-field statement would be vacuous.) This is the key arithmetic input to the disproof
of Erdős's unit distance conjecture (problem #90), proved in the Remarks paper via the
Hajir–Maire–Ramakrishna (2003) construction applied to a controlled pro-`2` Galois group.

A "completely split" rational prime `q` in `F` is one for which `(q : 𝓞 F)` is the product of
exactly `[F:ℚ]` distinct maximal ideals (equivalently, both the ramification index and the
residue degree of every prime above `q` are `1`).
-/
@[category research solved, AMS 11]
theorem prop_2_3_totally_real_tower :
    ∃ (rdBound : ℝ) (Q : Set ℕ), Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  sorry

end Arxiv.«2605.20695»
