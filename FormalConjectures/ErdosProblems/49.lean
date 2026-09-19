/-
Copyright 2025 The Formal Conjectures Authors.

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
- [Ta24d] Tao, Terence, *Monotone nondecreasing sequences of the Euler totient function*.
  Matematica (2024), 793-820.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos49

/-- The largest size of a set $A\subseteq\{1,\ldots,N\}$ on which Euler's totient function is
strictly increasing. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ StrictMonoOn Nat.totient (A : Set ℕ) ∧
    A.card = k}

/-- The largest size of a set $A\subseteq\{1,\ldots,N\}$ on which Euler's totient function is
non-decreasing. -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
    A.card = k}

/--
Let $A=\{a_1<\cdots<a_t\}\subseteq \{1,\ldots,N\}$ be such that $\phi(a_1)<\cdots<\phi(a_t)$.
The primes are such an example. Are they the largest possible? Can one show that
$\lvert A\rvert<(1+o(1))\pi(N)$ or even $\lvert A\rvert=o(N)$?

Erdős remarks that the last conjecture is probably easy, and that similar questions can be asked
about $\sigma(n)$.

Solved by Tao [Ta24d], who proved that
$$ \lvert A\rvert \leq \left(1+O\left(\frac{(\log\log x)^5}{\log x}\right)\right)\pi(x).$$

In [Er95c] Erdős further asks about the situation when $\phi(a_1)\leq \cdots \leq \phi(a_t)$.

See also [415](https://www.erdosproblems.com/415).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos49.lean#L120"]
theorem erdos_49 : answer(True) ↔ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (1 + ε) * Nat.primeCounting N := by
  sorry

/-- The weaker statement $\lvert A\rvert=o(N)$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos49.lean#L340"]
theorem erdos_49.variants.little_o :
    (fun N : ℕ ↦ (f N : ℝ)) =o[atTop] fun N ↦ (N : ℝ) := by
  sorry

/--
Tao [Ta24d] proved that
$\lvert A\rvert \leq \left(1+O\left(\frac{(\log\log N)^5}{\log N}\right)\right)\pi(N)$, even for
sets on which $\phi$ is merely non-decreasing.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos49.lean#L120"]
theorem erdos_49.variants.tao : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 10 ≤ N →
    (g N : ℝ) ≤ (1 + C * (Real.log (Real.log N) ^ 5 / Real.log N)) *
      Nat.primeCounting N := by
  sorry

/-- Are the primes the largest possible example, i.e. is $f(N) = \pi(N)$ for all $N \geq 2$? -/
@[category research open, AMS 11]
theorem erdos_49.variants.primes_maximal : answer(sorry) ↔
    ∀ N : ℕ, 2 ≤ N → f N = Nat.primeCounting N := by
  sorry

end Erdos49
