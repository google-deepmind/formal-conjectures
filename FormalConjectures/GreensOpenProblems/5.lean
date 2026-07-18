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
# Ben Green's Open Problem 5

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.5)
- [Ke97] Kedlaya, K. S., *Large product-free subsets of finite groups*, J. Combin. Theory
  Ser. A 77 (1997), no. 2, 339–343.
- [Ke09] Kedlaya, K. S., *Product-free subsets of groups, then and now*, Contemp. Math., 479,
  American Mathematical Society, Providence, RI, 2009, 169–177.
- [Go08] Gowers, W. T., *Quasirandom groups*, Combin. Probab. Comput. 17 (2008), no. 3,
  363–387.
-/

open scoped MatrixGroups

namespace Green5

/--
Which finite groups have the smallest biggest product-free sets?

We formalise this as: determine the largest exponent $\alpha$ such that every nontrivial
finite group of order $n$ contains a product-free set of size $\geq c n^{\alpha}$ for some
absolute constant $c > 0$. (The trivial group is excluded since its only product-free subset
is empty.) Kedlaya [Ke97] showed that $\alpha = 11/14$ is admissible, and Green suggests this
exponent may well be sharp; the candidate extremal family is the Ree groups ${}^2G_2(q)$,
$q = 3^{2m+1}$.
-/
@[category research open, AMS 5 20]
theorem green_5 :
    IsGreatest {α : ℝ | ∃ c > (0 : ℝ), ∀ (G : Type) [Group G] [Fintype G], Nontrivial G →
      ∃ S : Finset G, IsProductFree (S : Set G) ∧
        c * (Fintype.card G : ℝ) ^ α ≤ (S.card : ℝ)}
      answer(sorry) := by
  sorry

/--
Kedlaya [Ke97] observed, refining some work of Babai and Sós, that it follows from the
classification of finite simple groups that every finite group $G$ of order $n$ has a
product-free subset of size $\gg n^{11/14}$.
-/
@[category research solved, AMS 5 20]
theorem green_5.variants.kedlaya :
    ∃ c > (0 : ℝ), ∀ (G : Type) [Group G] [Fintype G], Nontrivial G →
      ∃ S : Finset G, IsProductFree (S : Set G) ∧
        c * (Fintype.card G : ℝ) ^ ((11 : ℝ) / 14) ≤ (S.card : ℝ) := by
  sorry

/--
A good model problem would be to determine the largest product-free subsets of
$\mathrm{SL}_2(\mathbb{F}_p)$.
-/
@[category research open, AMS 5 20]
theorem green_5.variants.sl_two (p : ℕ) [Fact p.Prime] :
    let S : ∀ q : ℕ, Set (SL(2, ZMod q)) := answer(sorry)
    MaximalFor (IsProductFree (M := SL(2, ZMod p))) Set.ncard (S p) := by
  sorry

/--
For the largest product-free subsets of $\mathrm{SL}_2(\mathbb{F}_p)$ of order $n$, the
best-known upper bound is $O(n^{8/9})$, due to Gowers [Go08].
-/
@[category research solved, AMS 5 20]
theorem green_5.variants.gowers_sl_two :
    ∃ C > (0 : ℝ), ∀ (p : ℕ) [Fact p.Prime], ∀ S : Finset SL(2, ZMod p),
      IsProductFree (S : Set SL(2, ZMod p)) →
      (S.card : ℝ) ≤ C * (Fintype.card SL(2, ZMod p) : ℝ) ^ ((8 : ℝ) / 9) := by
  sorry

end Green5
