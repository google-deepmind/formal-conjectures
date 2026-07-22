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
# Erdős Problem 206

*References:*
- [erdosproblems.com/206](https://www.erdosproblems.com/206)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique (1980).
- [Cu22] Curtiss, D. R., *On Kellogg's Diophantine Problem*. Amer. Math. Monthly (1922),
  380-387.
- [Er50b] Erdős, Pál, *On a Diophantine equation*. Mat. Lapok (1950), 192-210.
- [Na23] Nathanson, M., *Underapproximation by Egyptian fractions*. J. Number Theory (2023),
  208-234.
- [Ch23b] Chu, H. V., *A threshold for the best two-term underapproximation by Egyptian
  fractions*. arXiv:2306.12564 (2023).
- [Ko24b] Kovač, V., *On eventually greedy best underapproximations by Egyptian fractions*.
  arXiv:2406.07218 (2024).
-/

open MeasureTheory

namespace Erdos206

/- Formalization notes:
- The problem's greedy recursion ($R_{n+1}(x)=R_n(x)+1/m$ with $m$ minimal such that $m$ does
  not appear in $R_n(x)$ and the right-hand side is $<x$) is rendered as `EventuallyGreedy`:
  from some `n₀` on, the best `n`-term underapproximations form a nested chain given by the
  prefixes of a single strictly increasing sequence of denominators. The two are equivalent:
  if `S` is a best `n`-term underapproximation and `S ∪ {m}` a best `(n+1)`-term one, then `m`
  is forced to be the least `k ∉ S` with `egyptianSum S + 1/k < x` (a smaller admissible `k`
  would give a strictly larger `(n+1)`-term underapproximation), and conversely the greedy
  recursion produces exactly such a nested chain, with the appended denominators strictly
  increasing and exceeding `max S` (else swapping out `max S` would improve `S`).
- "for almost all $x$" is rendered as `∀ᵐ` with respect to Lebesgue measure restricted to
  $(0,\infty)$.
-/

/-- The Egyptian fraction sum: `∑_{m ∈ S} 1/m` for a finset of natural numbers. -/
noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (1 : ℝ) / m

/-- `S` is an Egyptian underapproximation of `x`: valid denominators (all positive) and sum < x. -/
def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  (∀ m ∈ S, 0 < m) ∧ egyptianSum S < x

/-- `S` achieves the best `n`-term Egyptian underapproximation of `x`,
i.e. `egyptianSum S` realises $R_n(x)$. -/
def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x → egyptianSum T ≤ egyptianSum S

/-- `x` has eventually greedy best Egyptian underapproximations: from some `n₀` on, the best
`n`-term underapproximations of `x` are the prefixes of a single strictly increasing sequence
of denominators, so each is obtained from the previous by appending the minimal admissible
denominator. -/
def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x

/--
Let $x>0$ be a real number. For any $n\geq 1$ let
\[R_n(x) = \sum_{i=1}^n\frac{1}{m_i}<x\]
be the maximal sum of $n$ distinct unit fractions which is $<x$.

Is it true that, for almost all $x$, for sufficiently large $n$, we have
\[R_{n+1}(x)=R_n(x)+\frac{1}{m},\]
where $m$ is minimal such that $m$ does not appear in $R_n(x)$ and the right-hand side is
$<x$? (That is, are the best underapproximations eventually always constructed in a 'greedy'
fashion?)

Kovač [Ko24b] has proved that this is false - in fact as false as possible: the set of
$x\in (0,\infty)$ for which the best underapproximations are eventually 'greedy' has Lebesgue
measure zero.
-/
@[category research solved, AMS 11]
theorem erdos_206 : answer(False) ↔
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), EventuallyGreedy x := by
  sorry

end Erdos206
