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
# Erdős Problem 497

*References:*
- [erdosproblems.com/497](https://www.erdosproblems.com/497)
- [Kl69] Kleitman, Daniel, *On Dedekind's problem: The number of monotone Boolean functions*.
  Proc. Amer. Math. Soc. (1969), 677-682.
-/

open Filter

namespace Erdos497

/--
The number of antichains in the power set of $[n]$: the number of families `𝒜` of subsets of
`Fin n` such that no member of `𝒜` is a subset of another. Note that `IsAntichain (· ⊆ ·)`
imposes the non-containment condition on distinct members only, which is the standard reading
of the problem (the literal condition applied with $A = B$ would be unsatisfiable, as
$A \subseteq A$).
-/
noncomputable def antichainCount (n : ℕ) : ℕ :=
  Nat.card {𝒜 : Finset (Finset (Fin n)) // IsAntichain (· ⊆ ·) (𝒜 : Set (Finset (Fin n)))}

/--
How many antichains in $[n]$ are there? That is, how many families of subsets of $[n]$ are
there such that, if $\mathcal{F}$ is such a family and $A,B\in \mathcal{F}$, then
$A\not\subseteq B$?

Sperner's theorem states that $\lvert \mathcal{F}\rvert \leq \binom{n}{\lfloor n/2\rfloor}$.
This is also known as Dedekind's problem. Resolved by Kleitman [Kl69], who proved that the
number of such families is
\[2^{(1+o(1))\binom{n}{\lfloor n/2\rfloor}}.\]
-/
@[category research solved, AMS 5 6,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos497.lean"]
theorem erdos_497 :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ n : ℕ, (antichainCount n : ℝ) = 2 ^ ((1 + o n) * (n.choose (n / 2) : ℝ)) := by
  sorry

-- Divergences from the hosted formalizations (statement-only lane):
--
-- * vs plby (Erdos497.lean, pinned above): plby's final `erdos_497` states
--   `Real.logb 2 (A n) ~[atTop] (n.choose (n / 2) : ℝ)` (`Asymptotics.IsEquivalent`).
--   We state the source's exponential form `A(n) = 2^{(1+o(1))·binom(n,⌊n/2⌋)}` directly,
--   with `o(1)` as `o =o[atTop] 1` per FC house style (cf. FC 285). The two are equivalent
--   since `antichainCount n ≥ 1` and `n.choose (n / 2) ≥ 1` for all `n`.
-- * vs plby and jayyhk: both define `A n` as `((univ.powerset).powerset.filter
--   (IsAntichain (· ⊆ ·) ·)).card` (classical decidability); we take `Nat.card` of the
--   corresponding subtype — the same count, with no `Decidable` instance needed. Their
--   auxiliary apparatus (the comparability graph `G n`, symmetric chain decompositions,
--   containers) belongs to the proof and is omitted here.
-- * vs jayyhk: jayyhk's final theorem writes `∃ ε, Filter.Tendsto ε atTop (nhds 0) ∧ …`;
--   `o =o[atTop] 1` is the same condition (`Asymptotics.isLittleO_one_iff`).
-- * vs problem text: `[n]` is rendered as `Fin n`, and the antichain condition is imposed
--   on distinct pairs only (see `antichainCount` docstring); both match the hosted
--   formalizations.

end Erdos497
