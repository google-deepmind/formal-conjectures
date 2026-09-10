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
# Erdős Problem 665

*References:*
- [erdosproblems.com/665](https://www.erdosproblems.com/665)
- [Er97f] Erdős, Paul, Some unsolved problems. Combinatorics, geometry and probability (Cambridge,
1993) (1997), 1-10.
- [ErLa82] Erdős, P. and Larson, J., On pairwise balanced block designs with the sizes of blocks as
uniform as possible. Annals of Discrete Mathematics (1982), 129-134.
- [ShSi85] S. S. Shrikhande and N. M. Singhi, On a problem of Erdős and Larson. Combinatorica
(1985), 351-358.
-/

namespace Erdos665

open Filter Asymptotics

/--
A pairwise balanced design for $\{1,\ldots,n\}$ is a collection of sets $A_1,\ldots,A_m\subseteq
\{1,\ldots,n\}$ such that $2\leq \lvert A_i\rvert <n$ and every pair of distinct elements $x,y\in
\{1,\ldots,n\}$ is contained in exactly one $A_i$. Is there a constant $C>0$ and, for all large $n$,
a pairwise balanced design such that
$$\lvert A_i\rvert > n^{1/2}-C$$
for all $1\leq i\leq m$?
-/
@[category research open, AMS 5]
theorem erdos_665 :
    answer(sorry) ↔ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∃ H : Finset (Finset (Fin n)), H.IsPairwiseBalancedDesign ∧
      ∀ e ∈ H, e.card < n ∧ Real.sqrt n - C < e.card := by
  sorry

end Erdos665
