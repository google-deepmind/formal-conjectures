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
# Erdős Problem 964

*References:*
- [erdosproblems.com/964](https://www.erdosproblems.com/964)
- [Er86b] Erdős, P., *Some problems on number theory*. Proceedings of the seventeenth Southeastern
  international conference on combinatorics, graph theory, and computing (Boca Raton, Fla.,
  1986), Congr. Numer. 54 (1986), 225-244.
- [Eb25] Eberhard, S., *Ratios of consecutive values of the divisor function*.
  [arXiv:2505.00727](https://arxiv.org/abs/2505.00727) (2025).
-/

@[expose] public section

open scoped ArithmeticFunction.sigma

namespace Erdos964

/-- $\tau(n+1)/\tau(n)$ as a real number, where $\tau = \sigma_0$ counts divisors. For $n = 0$
this is the junk value $0$, so the statements below use $n \geq 1$. -/
noncomputable def tauRatio (n : ℕ) : ℝ := (σ 0 (n + 1) : ℝ) / (σ 0 n : ℝ)

/-- For $n \geq 1$ the ratio $\tau(n+1)/\tau(n)$ is positive. -/
@[category API, AMS 11]
theorem tauRatio_pos {n : ℕ} (hn : 0 < n) : 0 < tauRatio n := by
  unfold tauRatio
  have h1 : 0 < σ 0 (n + 1) := ArithmeticFunction.sigma_pos_iff.2 (Nat.succ_pos n)
  have h2 : 0 < σ 0 n := ArithmeticFunction.sigma_pos_iff.2 hn
  exact div_pos (Nat.cast_pos.2 h1) (Nat.cast_pos.2 h2)

set_option linter.style.formal_proof_palomar false in
/--
Let $\tau(n)$ count the number of divisors of $n$. Is the sequence
$$\frac{\tau(n+1)}{\tau(n)}$$
everywhere dense in $(0,\infty)$?

The answer is yes, proved by Eberhard [Eb25].
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos964.lean#L1559"]
theorem erdos_964 : Set.Ioi (0 : ℝ) ⊆ closure (tauRatio '' Set.Ici 1) := by
  sorry

/--
Eberhard [Eb25] proved that the ratios $\tau(n+1)/\tau(n)$ attain every positive rational value
infinitely many times. Since the positive rationals are dense in $(0,\infty)$, this implies
`erdos_964`.
-/
@[category research solved, AMS 11]
theorem erdos_964.variants.eberhard (q : ℚ) (hq : 0 < q) :
    {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite := by
  sorry

end Erdos964
