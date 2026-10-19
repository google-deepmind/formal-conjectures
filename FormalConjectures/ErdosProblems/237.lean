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
# Erdős Problem 237

*References:*
- [erdosproblems.com/237](https://www.erdosproblems.com/237)
- [ChDi22] Chen, Y.-G. and Ding, Y., *On a conjecture of Erdős*.
  [arXiv:2201.10727](https://arxiv.org/abs/2201.10727) (2022).
- [Er50] Erdős, P., *On integers of the form $2^k+p$ and some related problems*.
  Summa Brasil. Math. (1950), 113-123.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos237

/--
`f A n` is the number of solutions to $n = p + a$ with $p$ prime and $a \in A$. A solution is
determined by $a$, so this counts the $a \in A$ with $a \leq n$ and $n - a$ prime.
-/
noncomputable def f (A : Set ℕ) (n : ℕ) : ℕ :=
  {a ∈ A | a ≤ n ∧ (n - a).Prime}.ncard

/--
Let $A\subseteq \mathbb{N}$ be a set such that $\lvert A\cap \{1,\ldots,N\}\rvert \gg \log N$ for
all large $N$. Let $f(n)$ count the number of solutions to $n=p+a$ for $p$ prime and $a\in A$. Is
it true that $\limsup f(n)=\infty$?

The answer is yes, as proved by Chen and Ding [ChDi22].

Here `A` may contain $0$. This changes each $f(n)$ by at most one, so it does not affect the
answer.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos237b.lean#L55"]
theorem erdos_237 : ∀ A : Set ℕ,
    (fun N : ℕ ↦ Real.log N) =O[atTop] (fun N ↦ ((A ∩ .Icc 1 N).ncard : ℝ)) →
    limsup (fun n ↦ (f A n : ℕ∞)) atTop = ⊤ := by
  sorry

/--
Chen and Ding [ChDi22] proved that the assumption
$\lvert A\cap \{1,\ldots,N\}\rvert \gg \log N$ can be replaced with the assumption that $A$ is
infinite.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos237b.lean#L55"]
theorem erdos_237.variants.infinite (A : Set ℕ) (hA : A.Infinite) :
    limsup (fun n ↦ (f A n : ℕ∞)) atTop = ⊤ := by
  sorry

/--
Erdős [Er50] proved the case $A=\{2^k : k\geq 0\}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos237b.lean#L55"]
theorem erdos_237.variants.pow_two :
    limsup (fun n ↦ (f (Set.range (2 ^ ·)) n : ℕ∞)) atTop = ⊤ := by
  sorry

end Erdos237
