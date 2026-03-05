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
# Erdős Problem 179

For integers $1 \leq k < \ell$, let $F_k(N, \ell)$ denote the minimum number of $k$-term
arithmetic progressions that an $N$-element subset of $\mathbb{N}$ must contain in order to
guarantee an $\ell$-term arithmetic progression. The problem asks whether
$F_3(N, 4) = o(N^2)$.

*Reference:* [erdosproblems.com/179](https://www.erdosproblems.com/179)

[FoPo20] Fox, J. and Pohoata, C., *Subset sums, completeness and colorings*. (2020).
-/

open Finset

namespace Erdos179

/--
A finite set of natural numbers contains a $k$-term arithmetic progression
if there exist natural numbers $a$ and $d$ with $d \geq 1$ such that
$a + i \cdot d \in A$ for all $0 \leq i < k$.
-/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≥ 1 ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/--
The number of $k$-term arithmetic progressions in $A$, counted as pairs $(a, d)$
with $d \geq 1$ such that $a + i \cdot d \in A$ for all $0 \leq i < k$.
-/
def numAP (A : Finset ℕ) (k : ℕ) : ℕ :=
  if h : A.Nonempty then
    let M := A.max' h
    ((Finset.Icc 0 M ×ˢ Finset.Icc 1 M).filter
      fun p => ∀ i ∈ Finset.range k, p.1 + i * p.2 ∈ A).card
  else 0

/--
Let $1 \leq k < \ell$ be integers and define $F_k(N, \ell)$ to be the minimum number of
$k$-term arithmetic progressions that an $N$-element set $A \subseteq \mathbb{N}$ must contain to
guarantee an $\ell$-term arithmetic progression. Is it true that $F_3(N, 4) = o(N^2)$?

Proved by Fox and Pohoata [FoPo20].
-/
@[category research solved, AMS 5]
theorem erdos_179 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ, A.card = N →
    (numAP A 3 : ℝ) ≥ ε * (N : ℝ) ^ 2 →
    ContainsAP A 4 := by
  sorry

/--
For every $\ell > 3$, $\lim_{N \to \infty} \log F_3(N, \ell) / \log N = 2$.
The nontrivial direction: for every $\varepsilon > 0$, for sufficiently large $N$,
there exists an $N$-element set with at least $N^{2 - \varepsilon}$ three-term arithmetic
progressions but no $\ell$-term arithmetic progression.

Proved by Fox and Pohoata [FoPo20].
-/
@[category research solved, AMS 5]
theorem erdos_179.variants.part2 :
    ∀ ℓ : ℕ, ℓ > 3 → ∀ ε : ℝ, ε > 0 → ε < 2 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∃ A : Finset ℕ, A.card = N ∧
    (numAP A 3 : ℝ) ≥ (N : ℝ) ^ (2 - ε) ∧
    ¬ContainsAP A ℓ := by
  sorry

end Erdos179
