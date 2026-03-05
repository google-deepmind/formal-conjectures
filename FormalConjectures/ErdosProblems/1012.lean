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
# Erdős Problem 1012

*Reference:* [erdosproblems.com/1012](https://www.erdosproblems.com/1012)

Let $k \geq 0$. Let $f(k)$ be the least integer such that every graph on $n \geq f(k)$
vertices with at least $\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle
of length $n-k$. Determine or estimate $f(k)$.

Erdős [Er62e] proved that $f(k)$ exists for all $k \geq 0$.
Ore [Or61] proved $f(0) = 1$ (every graph on $n \geq 1$ vertices with at least
$\binom{n-1}{2} + 2$ edges contains a Hamiltonian cycle).
Bondy [Bo71b] proved $f(1) = 1$.

Woodall [Wo72] proved that every graph on $n \geq 2k+3$ vertices with at least
$\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle of length $\ell$ for all
$3 \leq \ell \leq n-k$. This settles the question completely with $f(k) = 2k + 3$.
-/

open SimpleGraph

namespace Erdos1012

/-- A simple graph $G$ contains a cycle of length $m$ ($m \geq 3$) if there exist $m$
distinct vertices $v_0, \ldots, v_{m-1}$ such that $v_i$ is adjacent to
$v_{(i+1) \bmod m}$ for all $i$. -/
def ContainsCycleOfLength {V : Type*} (G : SimpleGraph V) (m : ℕ) (_ : m ≥ 3) : Prop :=
  ∃ (f : Fin m → V), Function.Injective f ∧
    ∀ i j : Fin m, j.val = (i.val + 1) % m → G.Adj (f i) (f j)

/--
Erdős Problem 1012 [Er62e] (solved by Woodall [Wo72]):

For every $k \geq 0$ and $n \geq 2k + 3$, every simple graph on $n$ vertices with at least
$\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle of length $\ell$ for every
$3 \leq \ell \leq n - k$.

In particular, taking $\ell = n - k$, this answers Erdős' original question with
$f(k) = 2k + 3$.
-/
@[category research solved, AMS 5]
theorem erdos_1012 (k n : ℕ) (hn : n ≥ 2 * k + 3)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1)
    (l : ℕ) (hl₁ : 3 ≤ l) (hl₂ : l ≤ n - k) :
    ContainsCycleOfLength G l hl₁ := by
  sorry

end Erdos1012
