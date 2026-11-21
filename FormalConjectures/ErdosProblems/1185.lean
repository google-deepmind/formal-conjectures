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
# Erdős Problem 1185

*References:*
- [erdosproblems.com/1185](https://www.erdosproblems.com/1185)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
- [Fu81] Furstenberg, H., *Recurrence in ergodic theory and combinatorial number theory*.
  M. B. Porter Lectures, Princeton University Press (1981), xi+203.
-/

@[expose] public section

namespace Erdos1185

/-- `HasAPWithStepInDiff k A B` says that `A` contains a non-trivial $k$-term arithmetic
progression $a, a+d, \ldots, a+(k-1)d$ whose common difference $d>0$ lies in $B-B$, that is,
$d=b_1-b_2$ with $b_1,b_2\in B$. Subtraction on `ℕ` is truncated, but $d>0$ forces $b_2<b_1$. -/
def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ (∀ j : ℕ, j < k → a + j * d ∈ A) ∧ ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = b₁ - b₂

/-- A set `B` with a single element has `B - B = {0}`, so it never gives a common difference
$d>0$. This is why the thresholds $m$ below are taken with $m\geq 1$ and matter only for
$m\geq 2$. -/
@[category API, AMS 5 11]
theorem not_hasAPWithStepInDiff_singleton (k : ℕ) (A : Finset ℕ) (b : ℕ) :
    ¬ HasAPWithStepInDiff k A {b} := by
  rintro ⟨a, d, hd, -, b₁, hb₁, b₂, hb₂, rfl⟩
  simp only [Finset.mem_singleton] at hb₁ hb₂
  omega

set_option linter.style.formal_proof_palomar false in
/--
Let $\delta>0$ and $k\geq 3$. Is it true that there exists $m\geq 1$ (depending only on $\delta$
and $k$) such that, for all large $N$, if $A,B\subseteq \{1,\ldots,N\}$ with
$\lvert A\rvert \geq \delta N$ and $\lvert B\rvert \geq m$ then there is a non-trivial $k$-term
arithmetic progression in $A$ whose common difference is in $B-B$?

A problem of Erdős and Mauldin [Er80, p. 92], who ask the case $k=3$ and say that the same
probably holds for $k$ terms. The answer is no, already for $k=3$: to disprove it suffices to give
an infinite set $B$ such that $B-B$ is not $2$-intersective (a set $S$ is $k$-intersective if
every subset of $\mathbb{N}$ with positive density contains an arithmetic progression of length
$k+1$ whose common difference is in $S$), which was provided by Furstenberg [Fu81]. The statement
below is the negation of the claim for all $\delta>0$ and $k\geq 3$, with $m$ chosen before the
threshold $N_0$ for "large $N$".
-/
@[category research solved, question, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1185.lean#L922"]
theorem erdos_1185 :
    ¬ (∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
          δ * (N : ℝ) ≤ (A.card : ℝ) → m ≤ B.card → HasAPWithStepInDiff k A B) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The answer is already negative for $k=3$: there is a density $\delta>0$ such that for every
$m\geq 1$ and every $N_0$ there are $N\geq N_0$ and $A,B\subseteq\{1,\ldots,N\}$ with
$\lvert A\rvert\geq\delta N$, $\lvert B\rvert\geq m$, and no non-trivial $3$-term arithmetic
progression in $A$ whose common difference is in $B-B$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1185.lean#L843"]
theorem erdos_1185.variants.k_three :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, 1 ≤ m → ∀ N₀ : ℕ, ∃ N : ℕ, ∃ A B : Finset ℕ,
      N₀ ≤ N ∧ A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
        δ * (N : ℝ) ≤ (A.card : ℝ) ∧ m ≤ B.card ∧ ¬ HasAPWithStepInDiff 3 A B := by
  sorry

end Erdos1185
