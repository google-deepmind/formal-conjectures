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
# Erdős Problem 551

*References:*
- [erdosproblems.com/551](https://www.erdosproblems.com/551)
- [BoEr73] Bondy, J. A. and Erdős, P., Ramsey numbers for cycles in graphs. J. Combin. Theory
  Ser. B (1973), 46-54.
- [Ni05] Nikiforov, V., The cycle-complete graph Ramsey numbers. Combin. Probab. Comput. (2005),
  349-370.
- [KLS21] Keevash, P., Long, E. and Skokan, J., Cycle-complete Ramsey numbers.
  Int. Math. Res. Not. IMRN (2021), 277-302.
-/

@[expose] public section

open Filter

namespace Erdos551

/--
Prove that
$$R(C_k,K_n)=(k-1)(n-1)+1$$
for $k\geq n\geq 3$ (except when $n=k=3$).

Asked by Erdős, Faudree, Rousseau, and Schelp.
This problem is #18 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_551 :
    ∀ (k n : ℕ), 3 ≤ n → n ≤ k → ¬(n = 3 ∧ k = 3) →
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k)
        (SimpleGraph.completeGraph (Fin n)) = (k - 1) * (n - 1) + 1 := by
  sorry

/--
For sufficiently large $n$ and every $k\geq n$, $R(C_k,K_n)=(k-1)(n-1)+1$.

Keevash, Long, and Skokan [KLS21] have proved this identity when
$k\geq C\frac{\log n}{\log\log n}$ for some constant $C$, thus establishing the conjecture
for sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_551.variants.sufficiently_large :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n ≤ k →
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k)
        (SimpleGraph.completeGraph (Fin n)) = (k - 1) * (n - 1) + 1 := by
  sorry

end Erdos551
