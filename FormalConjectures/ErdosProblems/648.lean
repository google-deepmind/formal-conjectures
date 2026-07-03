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
# Erdős Problem 648

*References:*
- [erdosproblems.com/648](https://www.erdosproblems.com/648)
- [Ca25b] S. Cambie, *On Erdős problem #648*. arXiv:2503.22691 (2025).
-/

open Filter Asymptotics

namespace Erdos648

/-
Divergences from the hosted theorems (details in statements/648/draft.json):
- the sequence range follows the problem text, `2 ≤ a_1 < ⋯ < a_t < n` (`Set.Ico 2 n`);
  both hosted theorems allow `0 < m ≤ n` (`Set.Ioc 0 n`), which admits `1` and `n`.
- `P` is the FC-house `Nat.maxPrimeFac`; the hosted files define
  `P n = (n.primeFactors.max).getD 1`. The two agree on `2 ≤ m`.
- the sequence is a strictly monotone `a : Fin t → ℕ` (FC house shape); the hosted
  theorems use a `List ℕ` with `IsChain`.
-/

/--
`g n` is the largest `t` such that there exist integers `2 ≤ a 0 < a 1 < ⋯ < a (t - 1) < n`
whose greatest prime factors are strictly decreasing. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {t | ∃ a : Fin t → ℕ, StrictMono a ∧ (∀ i, a i ∈ Set.Ico 2 n) ∧
    StrictAnti fun i => (a i).maxPrimeFac}

/--
Let $g(n)$ denote the largest $t$ such that there exist integers $2\leq a_1<a_2<\cdots <a_t <n$
such that \[P(a_1)>P(a_2)>\cdots >P(a_t)\] where $P(m)$ is the greatest prime factor of $m$.
Estimate $g(n)$.

Stijn Cambie has proved [Ca25b] \[g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}.\]
Cambie further asks whether there exists a constant $c$ such that
\[g(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}.\]
Cambie's proof shows that such a $c$ must satisfy $2\leq c\leq 2\sqrt{2}$.

The sequence $a_1<a_2<\cdots<a_t$ is packaged as a strictly monotone map `a : Fin t → ℕ`
with $2\leq a_i<n$, the greatest prime factor $P$ is `Nat.maxPrimeFac`, and $g(n)$ is the
supremum in `ℕ` of the achievable lengths $t$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos648.lean"]
theorem erdos_648 :
    (fun n => (g n : ℝ)) =Θ[atTop] fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) := by
  sorry

end Erdos648
