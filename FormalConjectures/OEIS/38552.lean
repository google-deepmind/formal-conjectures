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
# Conjectures associated with A038552

A038552 lists the largest squarefree number $k$ such that the imaginary quadratic field
$\mathbb{Q}(\sqrt{-k})$ has class number $n$.

The conjectures state that:
1. All terms are congruent to $19 \pmod{24}$.
2. This is also the largest absolute value of negative fundamental discriminant $d$ for
   class number $n$.
3. For even $n$, if $k$ is the largest odd number with $h(-k) = n$ and $k'$ is the largest
   even number with $h(-k') = n$, then $k > k'$. The $n$-th term is the larger of $k$ and
   $k'$, so this says that the $n$-th term is odd. Conjecture 1 implies it.

The squarefree condition in the definition is needed for the maximum to exist, since
$\mathbb{Q}(\sqrt{-k}) = \mathbb{Q}(\sqrt{-4k})$.

Conjecture 2 is not a restatement of the definition. Both maxima range over the same imaginary
quadratic fields, but they maximize different integers attached to those fields. A038552 uses
the squarefree radicand $k$, whereas the discriminant of $\mathbb{Q}(\sqrt{-k})$ is $-k$ for
$k \equiv 3 \pmod 4$ and $-4k$ otherwise. The map $k \mapsto |d|$ is not monotone: it sends $2$
to $8$ and $3$ to $3$. So conjecture 2 says that the largest term $k$ satisfies
$k \equiv 3 \pmod 4$, and that $4k' \le k$ for every $k' \equiv 1, 2 \pmod 4$ with class
number $n$.

*References:*
- [Sta67] Stark, Harold M. "A complete determination of the complex quadratic fields of
  class-number one." Michigan Mathematical Journal 14.1 (1967): 1-27.
- [oeis.org/A038552](https://oeis.org/A038552)
-/

open NumberField Polynomial

namespace OeisA38552

/-- The class number of the imaginary quadratic field $\mathbb{Q}(\sqrt{-k})$ equals $n$. -/
def HasClassNumber (k n : ℕ) : Prop :=
  ∃ (h : Irreducible (X ^ 2 + C (k : ℚ))),
  haveI := Fact.mk h
  NumberField.classNumber (AdjoinRoot (X ^ 2 + C (k : ℚ))) = n

/-- $k$ is maximal among squarefree numbers such that $\mathbb{Q}(\sqrt{-k})$ has class number $n$.
This defines the $n$-th term of A038552. -/
def IsA038552 (n k : ℕ) : Prop :=
  MaximalFor (fun m => Squarefree m ∧ HasClassNumber m n) id k

/-- The class number of the quadratic field with discriminant $d$. -/
noncomputable def classNumberOfDiscriminant (d : ℤ) : ℕ :=
  haveI := Classical.dec (Irreducible (X ^ 2 - C (d : ℚ)))
  if h : Irreducible (X ^ 2 - C (d : ℚ)) then
    haveI := Fact.mk h
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ)))
  else 0

/-- $|d|$ is the largest absolute value among negative fundamental discriminants
with class number $n$. -/
def IsLargestNegFundDiscrForClassNumber {n : ℕ} (absD : ℕ) : Prop :=
  IsGreatest {m : ℕ | IsFundamentalDiscr (-m : ℤ) ∧ classNumberOfDiscriminant (-m : ℤ) = n}
    absD

/-- The Stark-Heegner theorem [Sta67] implies that the squarefree $k > 0$ such that
$\mathbb{Q}(\sqrt{-k})$ has class number $1$ are exactly $\{1, 2, 3, 7, 11, 19, 43, 67, 163\}$. -/
@[category research solved, AMS 11]
theorem starkHeegner_classNumberOne :
    {k : ℕ | Squarefree k ∧ HasClassNumber k 1} = {1, 2, 3, 7, 11, 19, 43, 67, 163} := by
  sorry

/-- $\mathbb{Q}(\sqrt{-163})$ has class number $1$. -/
@[category API, AMS 11]
theorem hasClassNumber_163_1 : HasClassNumber 163 1 := by
  have h := starkHeegner_classNumberOne
  simp only [Set.ext_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact ((h 163).mpr (by decide)).2

/-- $163$ is the largest squarefree $k$ with class number $1$. -/
@[category test, AMS 11]
theorem isA038552_1_163 : IsA038552 1 163 := by
  refine ⟨⟨(by norm_num : Nat.Prime 163).squarefree, hasClassNumber_163_1⟩, ?_⟩
  intro m ⟨hm_sq, hm_class⟩ (hle : 163 ≤ m)
  have hm_in : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Set ℕ) :=
    starkHeegner_classNumberOne ▸ Set.mem_ofPred.mpr ⟨hm_sq, hm_class⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, id] at hm_in ⊢
  lia

/-
The values for other class numbers in A038552 come from the papers
* Duncan A. Buell, Small class numbers and extreme values of L-functions of quadratic fields,
Math. Comp., 31 (1977), 786-796.
* M. Watkins, Class numbers of imaginary quadratic fields, Mathematics of Computation 73 (2004),
pp. 907-938.
-/

/-- All terms of A038552 are congruent to $19 \pmod{24}$. -/
@[category research open, AMS 11]
theorem mod_24_of_isA038552 {n k : ℕ} (h : IsA038552 n k) : k % 24 = 19 := by
  sorry

/-- A038552 also gives the largest absolute value of negative fundamental discriminant
for each class number. -/
@[category research open, AMS 11]
theorem isA038552_eq_largestNegFundDisc {n k : ℕ} (h : IsA038552 n k) :
    IsLargestNegFundDiscrForClassNumber (n := n) k := by
  sorry

/-- For even class number $n$, the $n$-th term of A038552 is odd. The source states this as:
the largest odd squarefree $k$ with $h(-k) = n$ is greater than the largest even one. -/
@[category research open, AMS 11]
theorem odd_of_isA038552 {n k : ℕ} (hn : Even n) (h : IsA038552 n k) : Odd k := by
  sorry

end OeisA38552
