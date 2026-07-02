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
# Erdős Problem 498

*References:*
- [erdosproblems.com/498](https://www.erdosproblems.com/498)
- [Er45] Erdős, P., _On a lemma of Littlewood and Offord_. Bull. Amer. Math. Soc. (1945), 898-902.
- [Kl65] Kleitman, Daniel J., _On a lemma of Littlewood and Offord on the distribution of certain
  sums_. Math. Z. (1965), 251-259.
- [Kl70] Kleitman, Daniel J., _On a lemma of Littlewood and Offord on the distributions of linear
  combinations of vectors_. Advances in Math. (1970), 155-157.
-/

namespace Erdos498

-- Formalization notes.
--
-- * "an arbitrary disc of radius $1$" is formalized as the OPEN disc `Metric.ball c 1`. With the
--   verbatim hypothesis `1 ≤ ‖z i‖` the closed-disc reading is false (for `n = 1`, `z 0 = 1` the
--   closed unit disc centred at `0` contains both sums `±1`, while `Nat.choose 1 0 = 1`), and
--   Kleitman's theorem [Kl65] is about the interior of a circle of radius 1.
-- * "the number of sums" counts sign patterns `ε` (i.e. sums with multiplicity), the standard
--   reading in the Littlewood-Offord literature; it implies the bound for distinct sum values.
--
-- Divergences from the hosted proofs:
-- * plby (`littlewood_offord_complex_bound`) strengthens the norm hypothesis to `1 < ‖z i‖` and
--   uses the closed disc `Metric.closedBall c 1`; the problem text has `1 ≤ |z_i|`, which forces
--   the open disc (see above). It also binds the signs via a `let`-bound `Finset ℤ`.
-- * jayyhk (`erdos_498`) matches this statement mathematically (`1 ≤ ‖z i‖`, `Metric.ball c 1`,
--   `Set.ncard` over sign vectors, bound `n.choose (n / 2)`) but states the bound directly with
--   `let`-bound sets instead of the FC `answer(True) ↔` form.

/--
Let $z_1,\ldots,z_n\in\mathbb{C}$ with $1\leq \lvert z_i\rvert$ for $1\leq i\leq n$. Let $D$ be an
arbitrary disc of radius $1$. Is it true that the number of sums of the shape
\[\sum_{i=1}^n\epsilon_iz_i \textrm{ for }\epsilon_i\in \{-1,1\}\]
which lie in $D$ is at most $\binom{n}{\lfloor n/2\rfloor}$?

A strong form of the Littlewood-Offord problem. Erdős [Er45] proved this is true if
$z_i\in\mathbb{R}$, and for general $z_i\in\mathbb{C}$ proved a weaker upper bound of
\[\ll \frac{2^n}{\sqrt{n}}.\]
This was solved in the affirmative by Kleitman [Kl65], who also later generalised this to
arbitrary Hilbert spaces [Kl70].

See also [395].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos498.lean"]
theorem erdos_498 : answer(True) ↔
    ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, 1 ≤ ‖z i‖) → ∀ c : ℂ,
      {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧
        (∑ i, (ε i : ℂ) * z i) ∈ Metric.ball c 1}.ncard ≤ n.choose (n / 2) := by
  sorry

end Erdos498
