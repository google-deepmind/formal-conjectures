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
# Erdős Problem 54

*References:*
- [erdosproblems.com/54](https://www.erdosproblems.com/54)
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [BuEr85] Burr, S. A. and Erdős, P., *A Ramsey-type property in additive number theory*. Glasgow
  Math. J. (1985), 5-10.
- [CFP21] Conlon, D. and Fox, J. and Pham, H. T., *Subset sums, completeness and colorings*.
  arXiv:2104.14766 (2021).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos54

/--
A set of integers `A` is *Ramsey `r`-complete* if, whenever `A` is `r`-coloured, all sufficiently
large integers can be written as a monochromatic sum of distinct elements of `A`.
-/
def IsRamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ c : A → Fin r, ∀ᶠ n : ℕ in atTop,
    ∃ s : Finset A, (∃ i : Fin r, ∀ a ∈ s, c a = i) ∧ ∑ a ∈ s, (a : ℕ) = n

/--
A set of integers $A$ is Ramsey $2$-complete if, whenever $A$ is $2$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$. Burr and Erdős [BuEr85]
showed that there exists a constant $c>0$ such that it cannot be true that
$$\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2$$
for all large $N$ and that there exists a Ramsey $2$-complete $A$ such that for all large $N$
$$\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2N)^3.$$
Improve either of these bounds.

The stated bounds are due to Burr and Erdős [BuEr85]. Resolved by Conlon, Fox, and Pham [CFP21],
who constructed a Ramsey $2$-complete $A$ such that
$$\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^2$$
for all large $N$.

See also [55](https://www.erdosproblems.com/55) and [843](https://www.erdosproblems.com/843).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos54.lean#L37"]
theorem erdos_54 : ∃ A : Set ℕ, IsRamseyComplete 2 A ∧
    (fun N : ℕ ↦ ((A ∩ Set.Icc 1 N).ncard : ℝ)) =O[atTop] fun N ↦ Real.log N ^ 2 := by
  sorry

/--
Burr and Erdős [BuEr85] showed that there exists a constant $c>0$ such that no Ramsey
$2$-complete $A$ satisfies $\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2$ for all large
$N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54.variants.lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ A : Set ℕ, IsRamseyComplete 2 A →
      ∃ᶠ N : ℕ in atTop, c * Real.log N ^ 2 < (A ∩ Set.Icc 1 N).ncard := by
  sorry

/--
Burr and Erdős [BuEr85] showed that there exists a Ramsey $2$-complete $A$ such that for all
large $N$, $\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2N)^3$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54.variants.burr_erdos : ∃ A : Set ℕ, IsRamseyComplete 2 A ∧
    ∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) < (2 * Real.logb 2 N) ^ 3 := by
  sorry

end Erdos54
