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
# Erdős Problem 712

*Reference:* [erdosproblems.com/712](https://www.erdosproblems.com/712)

Determine, for any $k > r > 2$, the value of
$$\lim_{n \to \infty} \mathrm{ex}_r(n, K_k^r) / \binom{n}{r},$$
where $\mathrm{ex}_r(n, K_k^r)$ is the largest number of $r$-edges which can be placed on $n$
vertices so that there exists no set of $k$ vertices which is covered by all
$\binom{k}{r}$ possible $r$-edges.

Turán proved that, when $r = 2$, this limit is $\frac{1}{2}(1 - \frac{1}{k-1})$.

Erdős offered \$500 for the determination of this value for any fixed $k > r > 2$,
and \$1000 for 'clearing up the whole set of problems'.

See also [500] for the case $r = 3$ and $k = 4$.
-/

open Finset Filter

namespace Erdos712

/-- An $r$-uniform hypergraph on `Fin n` is $K_k^r$-free if every edge has exactly $r$
vertices and no $k$ vertices span all $\binom{k}{r}$ possible $r$-element subsets. -/
def IsKkrFree {n : ℕ} (r k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = r) ∧
  ∀ S : Finset (Fin n), S.card = k → ¬(S.powersetCard r ⊆ H)

/-- The $r$-uniform Turán number $\mathrm{ex}_r(n, K_k^r)$: the maximum number of $r$-element
subsets of an $n$-element set such that no $k$ vertices span all $\binom{k}{r}$
$r$-subsets. -/
noncomputable def exrKkr (r k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)), IsKkrFree r k H ∧ H.card = m}

/--
Erdős Conjecture (Problem 712) — Hypergraph Turán Densities:

For any $k > r > 2$, determine the value of the Turán density
$$\lim_{n \to \infty} \mathrm{ex}_r(n, K_k^r) / \binom{n}{r}.$$
-/
@[category research open, AMS 5]
theorem erdos_712 : ∀ k r : ℕ, 2 < r → r < k →
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => (exrKkr r k n : ℝ) / (Nat.choose n r : ℝ))
      atTop (nhds L) ∧ L = answer(sorry) := by
  sorry

end Erdos712
