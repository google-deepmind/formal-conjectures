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
public import FormalConjectures.ErdosProblems.«138»

/-!
# Erdős Problem 169

*References:*
- [erdosproblems.com/169](https://www.erdosproblems.com/169)
- [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Wa25] Walker, A., *Integer sets of large harmonic sum which avoid long arithmetic
  progressions*. [arXiv:2203.06045](https://arxiv.org/abs/2203.06045) (2025).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace Erdos169

/--
$f(k)$ is the supremum of $\sum_{n \in A} \frac{1}{n}$ as $A$ ranges over all sets of positive
integers which do not contain a $k$-term arithmetic progression. The sum is taken in `ℝ≥0∞`,
so $f(k) = \infty$ is allowed.
-/
noncomputable def f (k : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Set ℕ) (_ : 0 ∉ A) (_ : A.IsAPOfLengthFree k), ∑' n : A, ((n : ℕ) : ℝ≥0∞)⁻¹

/--
Let $k \geq 3$ and let $f(k)$ be the supremum of $\sum_{n \in A} \frac{1}{n}$ as $A$ ranges over
all sets of positive integers which do not contain a $k$-term arithmetic progression. Is
$$\lim_{k \to \infty} \frac{f(k)}{\log W(k)} = \infty,$$
where $W(k)$ is the van der Waerden number?
-/
@[category research open, question, AMS 5 11]
theorem erdos_169 :
    Tendsto (fun k ↦ f k / ENNReal.ofReal (Real.log (Erdos138.W k))) atTop (𝓝 ∞) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For every $k \geq 3$, $f(k) > \frac{2}{3} \log W(k)$.

It is trivial that $f(k) / \log W(k) \geq 1/2$. Erdős and Graham [ErGr79] asked for
$f(k) / \log W(k) > 1/2 + c$, and the problem page says that improving $1/2$ to any constant
$> 1/2$ is open. This variant gives $c = 1/6$ for every $k \geq 3$.

Put $N = W(k) - 1$ and take a $2$-colouring of $\{1, \dots, N\}$ with no monochromatic $k$-term
progression. Shift each colour class $C$ to a set $S$ with $0 = \min S$, and let $K$ be the set of
integers whose base $2N - 1$ digits all lie in $S$. By Walker's lifting argument [Wa25], $K + 1$
has no $k$-term progression. Counting by number of digits, its reciprocal sum is at least
$1 + (h - 1) / (1 - |S| / (2N - 1))$, where $h = \sum_{s \in S} \frac{1}{s + 1}$. Averaging over
the two classes gives $f(k) \geq \frac{2}{3} H_N - \frac{1}{3}$, and
$H_N > \log(N + 1) + \frac{1}{2}$ since $N \geq 8$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/0863e61864cfbb8306e453b8eb5f6d9fc48a669a/ErdosLean/Erdos169.lean"]
theorem erdos_169.variants.two_thirds (k : ℕ) (hk : 3 ≤ k) :
    ENNReal.ofReal (2 / 3 * Real.log (Erdos138.W k)) < f k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
There is a constant $c > 1/2$ such that $f(k) \geq c \log W(k)$ for every $k \geq 3$. This follows
from `erdos_169.variants.two_thirds` with $c = 2/3$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/0863e61864cfbb8306e453b8eb5f6d9fc48a669a/ErdosLean/Erdos169.lean"]
theorem erdos_169.variants.const_gt_half :
    ∃ c > (1 / 2 : ℝ), ∀ k ≥ 3, ENNReal.ofReal (c * Real.log (Erdos138.W k)) ≤ f k := by
  sorry

end Erdos169
