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
# Erdős Problem 999

The Duffin–Schaeffer conjecture: for any function `f : ℕ → ℝ`, almost every real number has
infinitely many coprime rational approximations `p/q` with `|α - p/q| < f(q)/q` if and only if
`∑ φ(q) f(q) / q` diverges. Proved by Koukoulopoulos and Maynard.

*Reference:* [erdosproblems.com/999](https://www.erdosproblems.com/999)

[Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
(1964), 52–65.

[KoMa20] Koukoulopoulos, D. and Maynard, J., _On the Duffin-Schaeffer conjecture_. Annals of
Mathematics (2) 191 (2020), 251–307.
-/

open MeasureTheory Set

namespace Erdos999

/--
The set of coprime integer-natural number pairs $(p, q)$ with $p \in \mathbb{Z}$, $q \in \mathbb{N}$,
$q > 0$, that approximate $\alpha$ within $f(q)/q$.
-/
def DuffinSchafferApprox (f : ℕ → ℝ) (α : ℝ) : Set (ℤ × ℕ) :=
  {pq | 0 < pq.2 ∧ Nat.Coprime (Int.natAbs pq.1) pq.2 ∧
    |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < f pq.2 / (pq.2 : ℝ)}

/--
Erdős Problem 999 (the Duffin-Schaeffer conjecture, now theorem):
For any function $f : \mathbb{N} \to \mathbb{R}$, the property that for almost all
$\alpha \in \mathbb{R}$, $|\alpha - p/q| < f(q)/q$ has infinitely many solutions with
$\gcd(p,q) = 1$, is equivalent to the divergence of
$\sum \varphi(q) \cdot f(q) / q$.

Proved by Koukoulopoulos and Maynard [KoMa20].
-/
@[category research solved, AMS 11]
theorem erdos_999 :
  ∀ f : ℕ → ℝ,
    (∀ᵐ α : ℝ, (DuffinSchafferApprox f α).Infinite) ↔
    (¬ Summable fun q : ℕ => (Nat.totient q : ℝ) * f q / (q : ℝ)) := by
  sorry

end Erdos999
