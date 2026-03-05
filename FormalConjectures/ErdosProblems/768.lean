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
# Erdős Problem 768

*Reference:* [erdosproblems.com/768](https://www.erdosproblems.com/768)

Let $A$ be the set of integers $n$ such that for every prime $p$ dividing $n$, there
exists a divisor $d > 1$ of $n$ with $d \equiv 1 \pmod{p}$. Is it true that there
exists $c > 0$ such that $|A \cap [1,N]| / N = \exp(-(c+o(1))\sqrt{\log N} \cdot \log \log N)$?

[Er74b] Erdős, P., *Problems and results on combinatorial number theory*.
-/

open Filter Classical

namespace Erdos768

/-- An integer $n$ is in the set $A$ if for every prime $p$ dividing $n$, there exists
some divisor $d > 1$ of $n$ with $d \equiv 1 \pmod{p}$. -/
def InSetA (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → ∃ d : ℕ, d > 1 ∧ d ∣ n ∧ d % p = 1

/-- Count of integers in $\{1, \ldots, N\}$ belonging to the set $A$. -/
noncomputable def countA (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => InSetA (n + 1))).card

/--
Erdős Problem 768 [Er74b]:

Is it true that there exists $c > 0$ such that
$$|A \cap [1,N]| / N = \exp(-(c + o(1)) \sqrt{\log N} \cdot \log \log N)?$$

Formalized as: there exists $c > 0$ such that
$-\log(|A \cap [1,N]| / N) / (\sqrt{\log N} \cdot \log(\log N)) \to c$ as $N \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_768 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    Tendsto
      (fun N : ℕ =>
        -Real.log ((countA N : ℝ) / (N : ℝ)) /
          (Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))))
      atTop (nhds c) := by
  sorry

end Erdos768
