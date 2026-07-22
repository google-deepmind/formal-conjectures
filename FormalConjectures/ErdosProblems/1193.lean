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

import FormalConjecturesUtil

/-!
# Erdős Problem 1193

*References:*
- [erdosproblems.com/1193](https://www.erdosproblems.com/1193)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

open AdditiveCombinatorics Set

namespace Erdos1193

/--
Let $A\subset \mathbb{N}$ and let $g(n)$ be a non-decreasing function of $n$ which is always $>0$.

Is the lower density of
\[\{ n : 1_A\ast 1_A(n)=g(n)\}\]
always $0$?

The answer is trivially no to both questions: indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$)
then $1_A\ast 1_A(n)=n+1$ for all $n$. Presumably Erdős had some additional restrictions on either
$g$ or $A$ in mind, but these are not recorded in [Er80].
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.parts.i : answer(False) ↔
    ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.lowerDensity = 0 := by
  sorry

/--
Let $A\subset \mathbb{N}$ and let $g(n)$ be a non-decreasing function of $n$ which is always $>0$.

Is the upper density of
\[\{ n : 1_A\ast 1_A(n)=g(n)\}\]
always $<c$ for some constant $c<1$?

The answer is trivially no to both questions: indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$)
then $1_A\ast 1_A(n)=n+1$ for all $n$. Presumably Erdős had some additional restrictions on either
$g$ or $A$ in mind, but these are not recorded in [Er80].
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.parts.ii : answer(False) ↔
    ∃ c < (1 : ℝ), ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.upperDensity < c := by
  sorry

/--
Indeed if $A=\mathbb{N}$ (assuming $0\in\mathbb{N}$) then $1_A\ast 1_A(n)=n+1$ for all $n$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1193.lean"]
theorem erdos_1193.variants.sumRep_univ (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  sorry

/--
Erdős writes the upper density can be positive, but he believes it is bounded away from $1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1193.variants.upper_density_pos :
    ∃ (A : Set ℕ) (g : ℕ → ℕ), Monotone g ∧ (∀ n, 0 < g n) ∧
      0 < {n : ℕ | sumRep A n = g n}.upperDensity := by
  sorry

end Erdos1193
