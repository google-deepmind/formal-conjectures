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
# Ben Green's Open Problem 2

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.2)
- [Er65] P. Erdős. Extremal problems in number theory, In Proc. Sympos. Pure Math., Vol. VIII,
  pages 181–189. Amer. Math. Soc., Providence, R.I., 1965.
- [Sa21] Sanders, Tom. "The Erdős–Moser Sum-free Set Problem." Canadian Journal of Mathematics 73.1
  (2021): 63-107.
- [Ru05] I. Z. Ruzsa, Sum-avoiding subsets. Ramanujan J., 9 (2005) (1-2):77–82.
- [Ch71] S. L. G. Choi. On a combinatorial problem in number theory. Proc. London Math. Soc. (3),
  23:629–642, 1971. doi:10.1112/plms/s3-23.4.629.
- [BSS00] A. Baltz, T. Schoen, and A. Srivastav. Probabilistic construction of small strongly
  sum-free sets via large Sidon sets. Colloq. Math., 86(2):171–176, 2000.
  doi:10.4064/cm-86-2-171-176.
-/

open Filter
open scoped Topology

namespace Green2

/--
The restricted sumset of a set $S$, denoted $S \hat{+} S$, is the set
$\lbrace s_1 + s_2 : s_1, s_2 \in S, s_1 \neq s_2 \rbrace$.
-/
def restrictedSumset (S : Finset ℤ) : Finset ℤ :=
  S.offDiag.image (fun p => p.1 + p.2)

/--
We define the construction from [Sa21, p1] as
$M(A) := \max \{|S| : S \subseteq A \text{ and } (S \hat{+} S) \cap A = \varnothing \}$.
-/
def maxRestrictedSumAvoidingSubsetSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter fun S => Disjoint (restrictedSumset S) A).sup Finset.card

/--
Let $A \subset \mathbf{Z}$ be a set of $n$ integers. Is there a set $S \subset A$ of size
$(\log n)^{100}$ such that the restricted sumset$S \hat{+} S$ is disjoint from $A$?
-/
@[category research open, AMS 11]
theorem green_2 : answer(sorry) ↔
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℤ, A.card = n →
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≥ (Real.log n) ^ 100 := by
  sorry

/--
From [Sa21] it is known that there is always such an S with $|S| \gt (\log |A|)^{1+c}$.
-/
@[category research solved, AMS 11]
theorem green_2_lower_bound_sanders :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℤ, A.card = n →
      maxRestrictedSumAvoidingSubsetSize A ≥ Real.log n ^ (1 + c) := by
  sorry

/--
From [Er65] it is known that $M(A) \le \frac{1}{3}|A| + O(1)$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_erdos :
    ∃ C : ℝ, ∀ A : Finset ℤ,
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card / 3 + C := by
  sorry

/-
TODO(jeangud): Add additional bounds on non-negative integers from Selfridge [Er65, p187], and
Choi [Er65, p190], and [BSS00].
-/

/--
From [Ch71] it is known that $M(A) \le |A|^{2/5 + o(1)}$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_choi :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)), ∀ A : Finset ℤ,
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card ^ (2 / 5 + o A.card) := by
  sorry

/--
From [Ru05] the best-known upper bound is $|S| \lt e^{C \sqrt{\log |A|}}$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_ruzsa :
    ∃ C > (0 : ℝ), ∀ A : Finset ℤ,
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) < Real.exp (C * Real.sqrt (Real.log A.card)) := by
  sorry

end Green2
