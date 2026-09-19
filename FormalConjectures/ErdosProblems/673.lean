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
# Erdős Problem 673

*References:*
- [erdosproblems.com/673](https://www.erdosproblems.com/673)
- [Er79e] Erdős, Paul, _Some unconventional problems in number theory_. Astérisque (1979), 73-82.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
-/

@[expose] public section

open Filter Asymptotics Real

namespace Erdos673

/-- If $1=d_1<\cdots <d_{\tau(n)}=n$ are the divisors of $n$ (here `Nat.nth (· ∣ n) i` is
$d_{i+1}$), then
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$ -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

/--
Let $1=d_1<\cdots <d_{\tau(n)}=n$ be the divisors of $n$ and
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$
Is it true that $G(n)\to \infty$ for almost all $n$?

The answer is yes: Tao observed that $\tau(n/m)/m\leq G(n)\leq \tau(n)$ for any $m\mid n$, so
that $G(n)$ behaves very similarly to $\tau(n)$. In [Er82e] Erdős recalls this conjecture and
observes that it is indeed trivial that $G(n)\to \infty$ for almost all $n$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.parts.i : answer(True) ↔ ∀ C : ℝ, {n : ℕ | C < G n}.HasDensity 1 := by
  sorry

/--
Can one prove an asymptotic formula for $\sum_{n\leq X}G(n)$?

Indeed $\sum_{n\leq X}G(n)\sim X\log X$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.parts.ii :
    (fun X : ℕ ↦ ∑ n ∈ Finset.Icc 1 X, G n) ~[atTop] fun X : ℕ ↦ (X : ℝ) * log X := by
  sorry

/-- Erdős writes it is 'easy' to prove $\frac{1}{X}\sum_{n\leq X}G(n)\to \infty$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.variants.average :
    Tendsto (fun X : ℕ ↦ (∑ n ∈ Finset.Icc 1 X, G n) / X) atTop atTop := by
  sorry

/-- Tao observed that, for any divisor $m\mid n$, $\frac{\tau(n/m)}{m} \leq G(n) \leq \tau(n)$. -/
@[category textbook, AMS 11]
theorem erdos_673.variants.tao (n m : ℕ) (hn : 0 < n) (hm : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card := by
  sorry

end Erdos673
