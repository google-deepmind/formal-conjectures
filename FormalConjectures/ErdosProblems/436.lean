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
# Erdős Problem 436

*Reference:* [erdosproblems.com/436](https://www.erdosproblems.com/436)

For prime $p$ and $k, m \geq 2$, let $r(k,m,p)$ be the minimal $r$ such that
$r, r+1, \ldots, r+m-1$ are all $k$-th power residues modulo $p$.
Let $\Lambda(k,m) = \limsup_{p \to \infty} r(k,m,p)$.

Hildebrand [Hi91] proved that $\Lambda(k,2)$ is finite for all $k \geq 2$.
Graham [Gr64g] proved that $\Lambda(k,\ell) = \infty$ for all $k \geq 2$ and $\ell \geq 4$.
Lehmer and Lehmer [LeLe62] proved that $\Lambda(k,3) = \infty$ for all even $k$.

The remaining open question is whether $\Lambda(k,3)$ is finite for all odd $k \geq 5$.
-/

namespace Erdos436

/-- A natural number $a$ is a $k$-th power residue modulo $p$ if there exists
$x$ such that $x^k = a$ in $\mathbb{Z}/p\mathbb{Z}$. -/
def IsKthPowerResidueMod (k : ℕ) (a : ℕ) (p : ℕ) : Prop :=
  ∃ x : ZMod p, x ^ k = (a : ZMod p)

/-- `LambdaFinite k m` asserts that $\Lambda(k,m)$ is finite: there exists a bound $R$
such that for all sufficiently large primes $p$, there exist $m$ consecutive
$k$-th power residues modulo $p$ starting at some $r$ with $1 \leq r \leq R$. -/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ R : ℕ, ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
    ∃ r : ℕ, r ≥ 1 ∧ r ≤ R ∧ ∀ j : ℕ, j < m → IsKthPowerResidueMod k (r + j) p

/-- Erdős Problem 436: Is $\Lambda(k,3)$ finite for all odd $k \geq 5$? That is, for any
odd $k \geq 5$, if $p$ is sufficiently large then there exist three consecutive $k$-th
power residues modulo $p$ in $[1, O_k(1)]$. -/
@[category research open, AMS 11]
theorem erdos_436 : answer(sorry) ↔
    ∀ k : ℕ, 5 ≤ k → k % 2 = 1 → LambdaFinite k 3 := by
  sorry

/-- Hildebrand [Hi91] proved that $\Lambda(k,2)$ is finite for all $k \geq 2$. For any
$k \geq 2$, if $p$ is sufficiently large then there exists a pair of consecutive $k$-th
power residues modulo $p$ in $[1, O_k(1)]$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.hildebrand (k : ℕ) (hk : 2 ≤ k) :
    LambdaFinite k 2 := by
  sorry

end Erdos436
