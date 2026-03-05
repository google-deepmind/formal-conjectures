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
# Erdős Problem 320

*Reference:* [erdosproblems.com/320](https://www.erdosproblems.com/320)

Let $S(N)$ count the number of distinct sums of the form $\sum_{n \in A} 1/n$
for $A \subseteq \{1, \ldots, N\}$. Estimate $S(N)$.

## Known Bounds

Bleicher and Erdős proved:
* **Lower bound** [BlEr75]: $\log S(N) \geq (N/\log N)(\log 2 \cdot \prod_{i=3}^{k} \log_i N)$
* **Upper bound** [BlEr76b]: $\log S(N) \leq (N/\log N)(\log_r N \cdot \prod_{i=3}^{r} \log_i N)$

where $\log_i$ denotes the $i$-fold iterated logarithm.

Bettin, Grenié, Molteni, and Sanna [BGMS25] improved the lower bound to:
$$\log S(N) \geq (N/\log N)(2 \log 2 (1 - 3/(2 \log_k N)) \cdot \prod_{i=3}^{k} \log_i N)$$

[BlEr75] Bleicher, M. N. and Erdős, P., *Denominators of unit fractions*, J. Number Theory (1975).

[BlEr76b] Bleicher, M. N. and Erdős, P., *Denominators of unit fractions II*, Illinois J. Math. (1976).

[BGMS25] Bettin, S., Grenié, L., Molteni, G., and Sanna, C. (2025).

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped Topology

namespace Erdos320

/-- The set of all unit-fraction subset sums from $\{1, \ldots, N\}$:
$\left\{ \sum_{n \in A} 1/n : A \subseteq \{1, \ldots, N\} \right\}$ as a finite set of
rationals. -/
noncomputable def unitFractionSums (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).powerset.image
    (fun A => A.sum (fun n => (1 : ℚ) / ↑n))

/-- $S(N)$ counts the number of distinct sums $\sum_{n \in A} 1/n$
for $A \subseteq \{1, \ldots, N\}$. -/
noncomputable def erdos320_S (N : ℕ) : ℕ := (unitFractionSums N).card

/--
**Erdős Problem 320** [ErGr80, p. 43]:

The ratio $\log S(N) / ((N / \log N) \cdot \log \log N)$ converges to a positive
constant as $N \to \infty$. Equivalently, $\log S(N) \sim L \cdot (N / \log N) \cdot \log \log N$
for some $L > 0$.
-/
@[category research open, AMS 5 11]
theorem erdos_320 :
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (fun N : ℕ => Real.log (erdos320_S N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))
        atTop (nhds L) := by
  sorry

end Erdos320
