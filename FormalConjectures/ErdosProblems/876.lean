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
# Erdős Problem 876

*References:*
- [erdosproblems.com/876](https://www.erdosproblems.com/876)
- [Er62c] Erdős, P., *Some remarks on number theory. III* (in Hungarian). Mat. Lapok 13 (1962),
  28-38. [PDF](https://www.renyi.hu/~p_erdos/1962-22.pdf)
- [Er75b] Erdős, P., *Problems and results in combinatorial number theory*. Journées Arithmétiques
  de Bordeaux (Conf., Univ. Bordeaux, 1974), Astérisque 24-25 (1975), 295-310.
  [PDF](https://www.renyi.hu/~p_erdos/1975-30.pdf)
- [Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976), Lecture Notes in Math. 626 (1977), 43-72.
  [PDF](https://www.renyi.hu/~p_erdos/1977-27.pdf)
- [Er98] Erdős, P., *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [DEM99] Deshouillers, J.-M., Erdős, P. and Melfi, G., *On a question about sum-free sequences*.
  Discrete Math. 200 (1999), 49-54.
- [LeOS77] Levine, E. and O'Sullivan, J., *An upper estimate for the reciprocal sum of a sum-free
  sequence*. Acta Arith. 34 (1977), 9-24.
- [Ab87] Abbott, H. L., *On sum-free sequences*. Acta Arith. 48 (1987), 93-96.

See also [erdosproblems.com/790](https://www.erdosproblems.com/790).
-/

@[expose] public section

open Filter

namespace Erdos876

/-- `A` is *sum-free* in the sense of Erdős: its elements are positive and no element is a sum of
distinct smaller elements of `A`. The condition `0 < a` fits $A\subset\mathbb{N}$ with
$\mathbb{N}=\{1,2,\ldots\}$ and makes the empty sum $0$ harmless. A single smaller element cannot
equal `a`, so only sums of $r\geq 2$ elements matter. This differs from the usual `IsSumFree`:
sums of any number of distinct smaller elements are forbidden, but $a=b+b$ is allowed. -/
def IsSubsetSumFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, 0 < a ∧ a ∉ subsetSums (A ∩ Set.Iio a)

/-- For an infinite set `A = {a₁ < a₂ < ⋯}`, `Nat.nth (· ∈ A) k` is $a_{k+1}$, because the
enumeration starts at index `0`. Hence `gap A n` is $a_{n+1}-a_n$ for $n\geq 1$. The value at
`n = 0` is junk and is never used, since the statements below only concern large `n`. -/
noncomputable def gap (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ A) n - Nat.nth (· ∈ A) (n - 1)

/-- `maxRecipSum` is the supremum of $\sum_{a\in A}1/a$ over infinite sum-free sets `A`. Only
convergent sums are taken (`HasSum`), so no junk value occurs. The set of values is nonempty (the
powers of $2$ give $2$) and bounded above by $103$ [Er62c], so `sSup` is the true supremum, which
may or may not be attained. -/
noncomputable def maxRecipSum : ℝ :=
  sSup {s : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
    HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s}

/-- The set `{1, 2, 3}` is not sum-free, since $3=1+2$. -/
@[category test, AMS 11]
theorem not_isSubsetSumFree_one_two_three : ¬ IsSubsetSumFree ({1, 2, 3} : Set ℕ) := by
  intro h
  refine (h 3 (by simp)).2 ⟨{1, 2}, ?_, by decide⟩
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> simp

/--
Let $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ be an infinite sum-free set - that is, there are no
solutions to
$$a=b_1+\cdots+b_r$$
with $b_1<\cdots<b_r<a\in A$. How small can $a_{n+1}-a_n$ be? Is it possible that
$a_{n+1}-a_n<n$?

The gap question is discussed by Erdős in [Er98]. We state the second question. The inequality
$a_{n+1}-a_n<n$ is required for all large $n$, because it fails for $n=1$. The first question is
vaguer and is not formalised.
-/
@[category research open, question, AMS 11]
theorem erdos_876.parts.i :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧ ∀ᶠ n : ℕ in atTop, gap A n < n := by
  sorry

def erdos_876.parts.ii.answer : ℝ := sorry

/--
In [Er75b] and [Er77c] Erdős asks to determine the maximum possible value of
$\sum_{n\in A}\frac{1}{n}$. Erdős had proved this is $<100$, and Sullivan had shown that this is
$<4$, and Sullivan conjectured the maximum is slightly larger than $2$ [Er77c, p. 52].

Here $A$ ranges over infinite sum-free sets, and the maximum is read as the supremum
`maxRecipSum`.
-/
@[category research open, question value, AMS 11]
theorem erdos_876.parts.ii : maxRecipSum = erdos_876.parts.ii.answer := by
  sorry

/--
Erdős [Er62c, Theorem I] proved that a sum-free set has density zero (restated as
[DEM99, Theorem 1]).
-/
@[category research solved, AMS 11]
theorem erdos_876.variants.density_zero (A : Set ℕ) (hA : A.Infinite) (hs : IsSubsetSumFree A) :
    A.HasDensity 0 := by
  sorry

/--
Erdős [Er62c, Theorem II] proved that $\sum_{a\in A}1/a$ converges and is $<103$ for every
infinite sum-free set $A$; see also [Er75b, p. 302] and [DEM99, p. 49]. The later paper
[Er77c, p. 52] states the bound as $100$.
-/
@[category research solved, AMS 11]
theorem erdos_876.variants.recip_sum_lt (A : Set ℕ) (hA : A.Infinite) (hs : IsSubsetSumFree A) :
    ∃ s : ℝ, s < 103 ∧ HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s := by
  sorry

/--
Let $R$ be the supremum of $\sum_j 1/n_j$ over sum-free sequences $\{n_j\}$. Levine and O'Sullivan
[LeOS77] proved $R<4$ (and $R>2.035$), and Abbott [Ab87] improved the lower bound to $R>2.064$,
as reported in [DEM99, p. 50].
-/
@[category research solved, AMS 11]
theorem erdos_876.variants.recip_sum_bounds : 2.064 < maxRecipSum ∧ maxRecipSum < 4 := by
  sorry

/--
Deshouillers, Erdős and Melfi [DEM99, Theorem 3] constructed an infinite sum-free set with
$a_{n+1}/a_n\to 1$.
-/
@[category research solved, AMS 11]
theorem erdos_876.variants.dem_ratio :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      Tendsto (fun k : ℕ ↦ (Nat.nth (· ∈ A) (k + 1) : ℝ) / (Nat.nth (· ∈ A) k : ℝ))
        atTop (nhds 1) := by
  sorry

/--
Deshouillers, Erdős and Melfi [DEM99, Theorem 4] proved that for every $\delta>0$ there is an
infinite sum-free set with $a_n\sim n^{3+\delta}$; we state the consequence $a_n\ll n^{3+\delta}$.
The site writes $a_n\sim n^{3+o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_876.variants.dem_polynomial (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      ∃ C : ℝ, ∀ k : ℕ, (Nat.nth (· ∈ A) k : ℝ) ≤ C * ((k : ℝ) + 1) ^ (3 + δ) := by
  sorry

end Erdos876
