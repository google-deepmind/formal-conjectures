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
# Erdős Problem 290

*References:*
- [erdosproblems.com/290](https://www.erdosproblems.com/290)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p.34.
- [vD24] van Doorn, W., *On the non-monotonicity of the denominator of generalized harmonic sums*.
  arXiv:2411.03073 (2024).
-/

namespace Erdos290

/-- The denominator (in lowest terms) of the partial harmonic sum
$\sum_{a \leq n \leq b}\frac{1}{n}$. -/
noncomputable def harmonicDen (a b : ℕ) : ℕ := (∑ n ∈ Finset.Icc a b, (1 : ℚ) / n).den

/--
Let $a\geq 1$. Must there exist some $b>a$ such that
$$\sum_{a\leq n\leq b}\frac{1}{n}=\frac{r_1}{s_1}\textrm{ and }
\sum_{a\leq n\leq b+1}\frac{1}{n}=\frac{r_2}{s_2},$$
with $(r_i,s_i)=1$ and $s_2<s_1$? If so, how does this $b(a)$ grow with $a$?

This was resolved in the affirmative by van Doorn [vD24], who proved $b=b(a)$ always exists, and in
fact $b(a) \ll a$. Indeed, if $a\in (3^k,3^{k+1}]$ then one can take $b=2\cdot 3^{k+1}-1$. van Doorn
also proves that $b(a)>a+(1/2-o(1))\log a$, and considers various generalisations of the original
problem.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem290.lean"]
theorem erdos_290 : answer(True) ↔
    (∀ a : ℕ, 1 ≤ a → ∃ b : ℕ, a < b ∧ harmonicDen a (b + 1) < harmonicDen a b) := by
  sorry

end Erdos290
