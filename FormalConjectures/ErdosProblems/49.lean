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
# Erdős Problem 49

*References:*
- [erdosproblems.com/49](https://www.erdosproblems.com/49)
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er95c] Erdős, Paul, *Some problems in number theory*. Octogon Math. Mag. (1995), 3-5.
- [Ta24d] Tao, Terence, *Monotone non-decreasing sequences of the Euler totient function*.
  La Matematica 3 (2024), 793-820. [arXiv:2309.02325](https://arxiv.org/abs/2309.02325)
-/

@[expose] public section

open Filter

namespace Erdos49

/--
Let $A = \{a_1 < \cdots < a_t\} \subseteq \{1, \ldots, N\}$ be such that
$\phi(a_1) < \cdots < \phi(a_t)$. The primes are such an example. Are they the largest possible?
Can one show that $|A| < (1 + o(1))\pi(N)$?

Tao [Ta24d] proved this. The $o(1)$ term is uniform in $A$: for every $\varepsilon > 0$ and all
large $N$, every such $A$ has $|A| < (1 + \varepsilon)\pi(N)$.
-/
@[category research solved, AMS 11]
theorem erdos_49 : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      StrictMonoOn Nat.totient (A : Set ℕ) → (A.card : ℝ) < (1 + ε) * Nat.primeCounting N := by
  sorry

/--
Let $A \subseteq \{1, \ldots, N\}$ be a set on which $\phi$ is strictly increasing.
Can one show that $|A| = o(N)$?

Erdős remarks that this weaker conjecture is probably easy. It follows from [Ta24d].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos49.lean#L254"]
theorem erdos_49.variants.littleO : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      StrictMonoOn Nat.totient (A : Set ℕ) → (A.card : ℝ) < ε * N := by
  sorry

/--
In [Er95c] Erdős also asks about the case $\phi(a_1) \le \cdots \le \phi(a_t)$.
Tao [Ta24d] proved that the bound $|A| < (1 + o(1))\pi(N)$ still holds.
-/
@[category research solved, AMS 11]
theorem erdos_49.variants.monotone : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      MonotoneOn Nat.totient (A : Set ℕ) → (A.card : ℝ) < (1 + ε) * Nat.primeCounting N := by
  sorry

/--
Tao [Ta24d] proved that if $A \subseteq \{1, \ldots, N\}$ with $N \ge 10$ and $\phi$ is
non-decreasing on $A$, then
$$|A| \le \left(1 + O\left(\frac{(\log\log N)^5}{\log N}\right)\right)\pi(N).$$
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos49.lean#L120"]
theorem erdos_49.variants.tao :
    ∃ C : ℝ, ∀ N ≥ 10, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      MonotoneOn Nat.totient (A : Set ℕ) →
        (A.card : ℝ) ≤
          (1 + C * Real.log (Real.log N) ^ 5 / Real.log N) * Nat.primeCounting N := by
  sorry

/--
Erdős remarks that similar questions can be asked about $\sigma(n)$. Tao [Ta24d] proved the
analogous bound: if $A \subseteq \{1, \ldots, N\}$ and $\sigma$ is strictly increasing on $A$,
then $|A| < (1 + o(1))\pi(N)$.
-/
@[category research solved, AMS 11]
theorem erdos_49.variants.sigma : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      StrictMonoOn (fun n => (ArithmeticFunction.sigma 1) n) (A : Set ℕ) →
        (A.card : ℝ) < (1 + ε) * Nat.primeCounting N := by
  sorry

/-- The primes are an example: $\phi$ is strictly increasing on the primes. -/
@[category test, AMS 11]
theorem erdos_49.test.primes : StrictMonoOn Nat.totient {p | p.Prime} := by
  intro p hp q hq hpq
  rw [Nat.totient_prime hp, Nat.totient_prime hq]
  have := hp.two_le
  omega

end Erdos49
