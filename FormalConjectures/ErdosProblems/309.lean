/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 309

*References:*
- [erdosproblems.com/309](https://www.erdosproblems.com/309)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Yo97] Yokota, Hisashi, *On number of integers representable as a sum of unit fractions. II*.
  J. Number Theory (1997), 162--169.
- [Cr99] Croot, III, Ernest S., *On some questions of Erdős and Graham about Egyptian fractions*.
  Mathematika (1999), 359-372.
- [Yo02] Yokota, Hisashi, *On the number of integers representable as sums of unit fractions.
  III*. J. Number Theory (2002), 351--372.
-/

@[expose] public section

open Filter Asymptotics Topology

namespace Erdos309

/-- The number of integers which can be written as the sum of distinct unit fractions with
denominators from $\{1,\ldots,N\}$. -/
noncomputable def F (N : ℕ) : ℕ :=
  {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ∑ n ∈ A, (1 / n : ℚ) = m}.ncard

/--
Let $N\geq 1$. How many integers can be written as the sum of distinct unit fractions with
denominators from $\{1,\ldots,N\}$? Are there $o(\log N)$ such integers?

If the number of such integers is $N(n)$ then it is trivial that $N(n)\leq \log n+O(1)$. Yokota
[Yo97] proved that $N(n)\geq \log n-O(\log\log n)$.

Croot [Cr99] proved that every integer at most
$$\leq \sum_{n\leq N}\frac{1}{n}-(\tfrac{9}{2}+o(1))\frac{(\log\log N)^2}{\log N}$$
can be so represented.

If $F(N)$ counts the number of integers which can be represented in this fashion, then the
current best lower bound known is
$$F(N) \geq \log N+\gamma -\left(\frac{\pi^2}{3}+o(1)\right)\frac{(\log\log N)^2}{\log N}$$
due to Yokota [Yo02].

The answer to the question is no: $F(N) \sim \log N$. Here $0$ (the empty sum) is counted.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos309.lean#L374"]
theorem erdos_309 : answer(False) ↔
    (fun N : ℕ => (F N : ℝ)) =o[atTop] fun N : ℕ => Real.log N := by
  sorry

/-- The number of representable integers satisfies $F(N) \sim \log N$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos309.lean#L374"]
theorem erdos_309.variants.asymptotic :
    Tendsto (fun N : ℕ => (F N : ℝ) / Real.log N) atTop (𝓝 1) := by
  sorry

end Erdos309
