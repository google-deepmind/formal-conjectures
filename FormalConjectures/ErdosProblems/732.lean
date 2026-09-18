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
# Erdős Problem 732

*References:*
- [erdosproblems.com/732](https://www.erdosproblems.com/732)
-/

namespace Erdos732

open Filter Asymptotics

/--
Call a sequence $1< X_1\leq \cdots \leq X_m\leq n$ block-compatible if there is a pairwise balanced
block design $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that $\lvert A_i\rvert=X_i$ for $1\leq
i\leq m$. (A pairwise block design means that every pair in $\{1,\ldots,n\}$ is contained in exactly
one of the $A_i$.) Are there necessary and sufficient conditions for $(X_i)$ to be block-compatible?
Is there some constant $c>0$ such that for all large $n$ there are
$$\geq \exp(c n^{1/2}\log n)$$
many block-compatible sequences for $\{1,\ldots,n\}$?
-/
@[category research open, AMS 5]
theorem erdos_732.parts.i :
    let P : ℕ → List ℕ → Prop := answer(sorry)
    ∀ (n : ℕ) (s : List ℕ), s ∈ Hypergraph.blockSizeProfiles n ↔ P n s := by
  sorry

/--
Is there some constant $c>0$ such that for all large $n$ there are at least
$\exp(c n^{1/2}\log n)$ block-compatible sequences?

Alon has proved there are at least $2^{(\frac{1}{2}+o(1))n^{1/2}\log n}$ many sequences
which are block-compatible for $n$.
-/
@[category research solved, AMS 5]
theorem erdos_732.parts.ii :
    answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    Real.exp (c * Real.sqrt n * Real.log n) ≤ (Hypergraph.blockSizeProfiles n).card := by
  sorry

end Erdos732
