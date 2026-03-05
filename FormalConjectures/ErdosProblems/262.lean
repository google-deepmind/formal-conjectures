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
# Erdős Problem 262

*Reference:* [erdosproblems.com/262](https://www.erdosproblems.com/262)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[Er88c] Erdős, P. (1988).

[Er75c] Erdős, P. (1975).

[Ha91] Hančl, J. (1991).
-/

open Filter

namespace Erdos262

/-- A strictly increasing sequence of positive integers is an irrationality sequence
if for every sequence of positive integers $t$, the sum $\sum 1/(t_n \cdot a_n)$ is irrational. -/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (∀ n, 0 < a n) ∧
  ∀ t : ℕ → ℕ, (∀ n, 0 < t n) →
    Irrational (∑' n, (1 : ℝ) / ((t n : ℝ) * (a n : ℝ)))

/--
Erdős Problem 262 [ErGr80] [Er88c]:
Suppose $a_1 < a_2 < \cdots$ is a sequence of positive integers such that for all
sequences of positive integers $t_n$, the sum $\sum 1/(t_n a_n)$ is irrational
(i.e., $a$ is an irrationality sequence). How slowly can $a_n$ grow?

An example of such a sequence is $a_n = 2^{2^n}$ (Erdős [Er75c]), while
a non-example is $a_n = n!$.

Hančl [Ha91] proved that any irrationality sequence must satisfy
$$\limsup_{n \to \infty} \frac{\log_2 \log_2 a_n}{n} \geq 1,$$
i.e., for all $c < 1$, $\log_2(\log_2(a_n)) > cn$ for infinitely many $n$.
-/
@[category research solved, AMS 11]
theorem erdos_262
    (a : ℕ → ℕ) (ha : IsIrrationalitySequence a)
    (c : ℝ) (hc : c < 1) :
    Filter.Frequently (fun (n : ℕ) => c * (↑n : ℝ) < Real.logb 2 (Real.logb 2 (↑(a n) : ℝ)))
      atTop := by
  sorry

end Erdos262
