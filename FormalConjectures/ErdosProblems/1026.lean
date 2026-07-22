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
# Erdős Problem 1026

*References:*
- [erdosproblems.com/1026](https://www.erdosproblems.com/1026)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Ha57] Hanani, Haim, *On the number of monotonic subsequences*. Bull. Res. Council Israel
  Sect. F (1957/58), 11-13.
- [St95] Steele, J. Michael, *Variations on the monotone subsequence theme of Erdős and
  Szekeres*. (1995), 111-131.
- [TWY16] Tidor, J. and Wang, V. and Yang, B., *$1$-color avoiding paths, special tournaments,
  and incidence geometry*. arXiv:1608.04153 (2016).
- [Wa17] Wagner, Adam Zsolt, *Large subgraphs in rainbow-triangle free colorings*. J. Graph
  Theory (2017), 141-148.
-/

namespace Erdos1026

open Filter

/--
The set of sums $\sum x_{i_r}$, where $x_{i_1},\ldots,x_{i_r}$ ranges over the monotonic
subsequences of the sequence $x_1,\ldots,x_n$.
-/
def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

/--
The set of constants $c$ such that, for all sequences of $n$ distinct real numbers
$x_1,\ldots,x_n$,
\[
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
\]
(where the maximum is taken over all monotonic subsequences).
-/
def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

/--
Let $x_1,\ldots,x_n$ be a sequence of distinct real numbers. Determine
\[
\max\left(\sum x_{i_r}\right),
\]
where the maximum is taken over all monotonic subsequences.

This is as Erdős posed the problem in [Er71], which is rather ambiguous. Discussion between
several users in the comments section has led to the following precise possible question, as
posed by van Doorn:

What is the largest constant $c$ such that, for all sequences of $n$ real numbers
$x_1,\ldots,x_n$,
\[
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
\]
(where again the maximum is taken over all monotonic subsequences)?

Cambie makes the stronger conjecture that if $x_1,\ldots,x_{k^2}$ are distinct positive real
numbers with $\sum x_i=1$ then there is always a monotonic subsequence with sum at least $1/k$.

This stronger conjecture appears to have been first proved by Tidor, Wang, and Yang [TWY16],
and is also implicit in work of Wagner [Wa17]. A proof was given and formalised by Aristotle
(see the comments), with an alternative proof provided by Chan. In particular, this shows that
$c=1$.
-/
@[category research solved, AMS 5]
theorem erdos_1026 : IsGreatest admissibleConstants answer(sorry) := by
  sorry

/--
In particular, this shows that $c=1$.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.eq_one : IsGreatest admissibleConstants 1 := by
  sorry

/--
A construction of Cambie in the comments shows that $c\leq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.upper_bound : 1 ∈ upperBounds admissibleConstants := by
  sorry

/--
Hanani [Ha57] showed that every sequence is the disjoint union of at most
$(\sqrt{2}+o(1))\sqrt{n}$ many monotonic subsequences, whence $c\geq 1/\sqrt{2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.lower_bound : 1 / Real.sqrt 2 ∈ admissibleConstants := by
  sorry

/--
Hanani [Ha57] showed that every sequence is the disjoint union of at most
$(\sqrt{2}+o(1))\sqrt{n}$ many monotonic subsequences.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.hanani (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
      ∃ (m : ℕ) (I : Fin m → Finset (Fin n)),
        (∀ j, MonotoneOn x ↑(I j) ∨ AntitoneOn x ↑(I j)) ∧
        (Pairwise fun j k => Disjoint (I j) (I k)) ∧
        (Finset.univ : Finset (Fin m)).biUnion I = Finset.univ ∧
        (m : ℝ) ≤ (Real.sqrt 2 + ε) * Real.sqrt (n : ℝ) := by
  sorry

/--
Cambie makes the stronger conjecture that if $x_1,\ldots,x_{k^2}$ are distinct positive real
numbers with $\sum x_i=1$ then there is always a monotonic subsequence with sum at least $1/k$.
This is a weighted-form of the Erdős-Szekeres theorem, and is also mentioned (as an open
question) in a survey on the latter by Steele [St95].

This stronger conjecture appears to have been first proved by Tidor, Wang, and Yang [TWY16],
and is also implicit in work of Wagner [Wa17]. A proof was given and formalised by Aristotle
(see the comments), with an alternative proof provided by Chan.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.weighted_erdos_szekeres (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ)
    (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S := by
  sorry

end Erdos1026
