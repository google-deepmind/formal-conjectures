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
# Erdős Problem 673

*Reference:* [erdosproblems.com/673](https://www.erdosproblems.com/673)

Let $1 = d_1 < \cdots < d_{\tau(n)} = n$ be the divisors of $n$ and
$$G(n) = \sum_{1 \leq i < \tau(n)} d_i / d_{i+1}.$$

Is it true that $G(n) \to \infty$ for almost all $n$? Can one prove an asymptotic
formula for $\sum_{n \leq X} G(n)$?

Erdős writes it is 'easy' to prove $(1/X) \sum_{n \leq X} G(n) \to \infty$.

Terence Tao observed that for any divisor $m \mid n$,
$\tau(n/m) / m \leq G(n) \leq \tau(n)$,
and hence for example $\tau(n)/4 \leq G(n) \leq \tau(n)$ for even $n$. It follows easily
that $G(n)$ grows on average and tends to infinity for almost all $n$.

Erdős and Tenenbaum proved that $G(n)/\tau(n)$ has a continuous distribution
function.

[Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979).

[Er82e] Erdős, P., _Some new problems and results in number theory_ (1982).
-/

open Filter

namespace Erdos673

/-- The sorted list of divisors of $n$ in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- $G(n) = \sum_{1 \leq i < \tau(n)} d_i / d_{i+1}$, where $d_1 < \cdots < d_{\tau(n)}$ are the
divisors of $n$ in increasing order. This is the sum of ratios of consecutive
divisors. -/
noncomputable def erdosG (n : ℕ) : ℝ :=
  let divs := sortedDivisors n
  ((divs.zip divs.tail).map (fun p => (p.1 : ℝ) / (p.2 : ℝ))).sum

/-- The natural density of a set $A \subseteq \mathbb{N}$ is zero. -/
def HasNaturalDensityZero (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop :=
  Tendsto
    (fun N : ℕ => (((Finset.range N).filter (· ∈ A)).card : ℝ) / (N : ℝ))
    atTop (nhds 0)

/--
Erdős Problem 673, Part 1 [Er79e, Er82e]:

$G(n) \to \infty$ for almost all $n$, i.e., for every $M$, the set of $n$ with $G(n) \leq M$
has natural density zero.
-/
@[category research solved, AMS 11]
theorem erdos_673 :
    answer(True) ↔ ∀ M : ℝ, HasNaturalDensityZero {n : ℕ | erdosG n ≤ M} := by
  sorry

/--
Erdős Problem 673, Part 2 [Er79e, Er82e]:

$(1/X) \cdot \sum_{n \leq X} G(n) \to \infty$ as $X \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_673.variants.average :
    Tendsto
      (fun X : ℕ => (Finset.sum (Finset.range X) erdosG) / (X : ℝ))
      atTop atTop := by
  sorry

end Erdos673
