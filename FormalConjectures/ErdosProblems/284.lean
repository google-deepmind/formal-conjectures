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
# Erdős Problem 284

*References:*
- [erdosproblems.com/284](https://www.erdosproblems.com/284)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique 28 (1980).
- [Cr01] Croot, III, Ernest S., *On unit fractions with denominators in short intervals*. Acta
  Arith. 99 (2001), 99-114. [arXiv:math/9904181](https://arxiv.org/abs/math/9904181)
-/

@[expose] public section

open Filter

namespace Erdos284

/-- `IsRepresentation k n` says that `n 0 < n 1 < ⋯ < n (k - 1)` are positive integers with
$$1 = \frac{1}{n_0} + \cdots + \frac{1}{n_{k-1}}.$$
The sum is taken in `ℝ`. -/
def IsRepresentation (k : ℕ) (n : Fin k → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The possible values of the first denominator `n 0` in a representation with exactly `k`
terms. This set is empty for `k = 0` and `k = 2`, and equal to `{1}` for `k = 1`. -/
def firstDenominators (k : ℕ) : Set ℕ :=
  {m | ∃ (hk : 0 < k) (n : Fin k → ℕ), IsRepresentation k n ∧ n ⟨0, hk⟩ = m}

/-- $f(k)$, the maximal first denominator in a representation with exactly `k` terms, as a
`sSup`. If no representation exists (`k = 0` and `k = 2`), the value is the junk value `0`.
Otherwise the set is bounded by `k`, because $1/n_i \leq 1/n_0$ gives $n_0 \leq k$, so `f k` is
its maximum. -/
noncomputable def f (k : ℕ) : ℕ :=
  sSup (firstDenominators k)

/-- For all large `k`, `f k` is the greatest element of `firstDenominators k`. -/
@[category API, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos284.lean#L82"]
theorem eventually_f_isGreatest :
    ∀ᶠ k : ℕ in atTop, IsGreatest (firstDenominators k) (f k) := by
  sorry

/--
Let $f(k)$ be the maximal value of $n_1$ such that there exist $n_1<n_2<\cdots <n_k$ with
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.$$
Is it true that
$$f(k)=(1+o(1))\frac{k}{e-1}?$$

Asked by Erdős and Graham [ErGr80, p. 33]. We state it as $f(k)/k\to 1/(e-1)$, which is
equivalent. Essentially solved by Croot [Cr01], who showed that for any $N>1$ there exists some
$k\geq 1$ and
$$N<n_1<\cdots <n_k \leq (e+o(1))N$$
with $1=\sum \frac{1}{n_i}$. See also [erdosproblems.com/286](https://www.erdosproblems.com/286).
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos284.lean#L97"]
theorem erdos_284 :
    Tendsto (fun k : ℕ ↦ (f k : ℝ) / k) atTop (nhds (1 / (Real.exp 1 - 1))) := by
  sorry

end Erdos284
