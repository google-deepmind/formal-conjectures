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
# Erdős Problem 121

*References:*
- [erdosproblems.com/121](https://www.erdosproblems.com/121)
- [Er94b] Erdős, Paul, *Some problems in number theory, combinatorics and combinatorial geometry*.
  Math. Pannon. (1994), 261-269.
- [Er97] Erdős, Paul, *Problems in number theory*. New Zealand J. Math. (1997), 155-160.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [ESS95] Erdős, P. and Sárközy, A. and Sós, V. T., *On product representations of powers. I*.
  European J. Combin. (1995), 567-588.
- [Er38] P. Erdős, *On sequences of integers no one of which divides the product of two others
  and on related problems*. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.
- [Ta24] Tao, T., *On product representations of squares*. arXiv:2405.11610 (2024).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos121

/-- $F_k(N)$ is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no
$k$ many distinct elements of $A$ is a square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = k → ¬ IsSquare (∏ n ∈ S, n)) ∧ A.card = m}

/--
Let $F_{k}(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no
$k$ many distinct elements of $A$ is a square. Is $F_5(N)=(1-o(1))N$?

Conjectured by Erdős, Sós, and Sárközy [ESS95], who proved
$F_2(N)=\left(\frac{6}{\pi^2}+o(1)\right)N$, $F_3(N) = (1-o(1))N$, and also established
asymptotics for $F_k(N)$ for all even $k\geq 4$ (in particular $F_k(N)\asymp N/\log N$ for all
even $k\geq 4$). Erdős [Er38] earlier proved that $F_4(N)=o(N)$ - indeed, if
$\lvert A\rvert \gg N$ and $A\subseteq \{1,\ldots,N\}$ then there is a non-trivial solution to
$ab=cd$ with $a,b,c,d\in A$.

This problem was answered in the negative by Tao [Ta24], who proved that for any $k\geq 4$ there
is some constant $c_k>0$ such that $F_k(N) \leq (1-c_k+o(1))N$.

See also [888](https://www.erdosproblems.com/888).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos121.lean#L87"]
theorem erdos_121 : answer(False) ↔ (fun N : ℕ => (F 5 N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ) := by
  sorry

/-- More generally, is $F_{2k+1}(N)=(1-o(1))N$? This is false for all $k \geq 2$ by Tao's
theorem [Ta24]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos121.lean#L87"]
theorem erdos_121.variants.odd : answer(False) ↔ ∀ k : ℕ, 1 ≤ k →
    (fun N : ℕ => (F (2 * k + 1) N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ) := by
  sorry

/-- Tao [Ta24] proved that for any $k\geq 4$ there is some constant $c_k>0$ such that
$F_k(N) \leq (1-c_k+o(1))N$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos121.lean#L87"]
theorem erdos_121.variants.tao (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N := by
  sorry

/-- Erdős, Sós, and Sárközy [ESS95] proved $F_3(N) = (1-o(1))N$. -/
@[category research solved, AMS 11]
theorem erdos_121.variants.three : (fun N : ℕ => (F 3 N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ) := by
  sorry

/-- Erdős, Sós, and Sárközy [ESS95] proved $F_2(N)=\left(\frac{6}{\pi^2}+o(1)\right)N$. -/
@[category research solved, AMS 11]
theorem erdos_121.variants.two :
    (fun N : ℕ => (F 2 N : ℝ)) ~[atTop] fun N : ℕ => 6 / Real.pi ^ 2 * N := by
  sorry

end Erdos121
