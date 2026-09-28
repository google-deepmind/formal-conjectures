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
# Erdős Problem 270

*References:*
- [erdosproblems.com/270](https://www.erdosproblems.com/270)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ha75] Hansen, E. R., *A Table of Series and Products*. Prentice-Hall (1975), 87.
- [CrKo25] T. Crmarić and V. Kovač, *On the irrationality of certain super-polynomially decaying
  series*. arXiv:2504.18712 (2025).
-/

@[expose] public section

open Filter

namespace Erdos270

/-- The series $\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$, indexed from $0$. -/
noncomputable def series (f : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹

/--
Let $f(n)\to \infty$ as $n\to \infty$. Is it true that
$$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$$
is irrational?

Erdős and Graham [ErGr80] write 'the answer is almost surely in the affirmative if $f(n)$ is
assumed to be nondecreasing'. Even the case $f(n)=n$ is unknown, although Hansen [Ha75] has
shown that
$$\sum_n \frac{1}{\binom{2n}{n}}=\sum_n \frac{n!}{(n+1)\cdots (n+n)}=\frac{1}{3}+\frac{2\pi}{3^{5/2}}$$
is transcendental.

Crmarić and Kovač [CrKo25] have shown that the answer to this question is no in a strong sense:
for any $\alpha \in (0,\infty)$ there exists a function $f:\mathbb{N}\to\mathbb{N}$ such that
$f(n)\to \infty$ as $n\to\infty$ and
$$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}=\alpha.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos270.lean#L1027"]
theorem erdos_270 : answer(False) ↔
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop → Irrational (series f) := by
  sorry

/--
Crmarić and Kovač [CrKo25]: for any $\alpha \in (0,\infty)$ there exists a function
$f:\mathbb{N}\to\mathbb{N}$ such that $f(n)\to \infty$ as $n\to\infty$ and
$$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}=\alpha.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos270.lean#L1009"]
theorem erdos_270.variants.every_value (α : ℝ) (hα : 0 < α) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α := by
  sorry

/--
It is still possible that this sum is always irrational if $f$ is assumed to be non-decreasing;
Crmarić and Kovač [CrKo25] show that the set of the possible values of such a sum has Lebesgue
measure zero.
-/
@[category research open, AMS 11]
theorem erdos_270.variants.monotone : answer(sorry) ↔
    ∀ f : ℕ → ℕ, Monotone f → Tendsto f atTop atTop → Irrational (series f) := by
  sorry

/-- Even the case $f(n)=n$ is unknown. -/
@[category research open, AMS 11]
theorem erdos_270.variants.linear : answer(sorry) ↔ Irrational (series id) := by
  sorry

end Erdos270
