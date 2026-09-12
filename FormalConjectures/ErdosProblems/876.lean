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
# Erdős Problem 876

*References:*
- [erdosproblems.com/876](https://www.erdosproblems.com/876)
- [DEM99] Deshouillers, Jean-Marc and Erdős, Paul and Melfi, Giuseppe, *On a question about sum-free
  sequences*. Discrete Math. (1999), 49--54.
- [Er62c] Erdős, Pál, *Some remarks on number theory. {III}*. Mat. Lapok (1962), 28--38.
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées Arithmétiques
  de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [LuSc00] Łuczak, Tomasz and Schoen, Tomasz, *On the maximal density of sum-free sets*. Acta Arith.
  (2000), 225--229.
-/

open Filter Real Set Asymptotics
open scoped Topology

namespace Erdos876

/--
A set $A\subseteq\mathbb{N}$ is subset-sum-free if no element of $A$ is a sum of two or more
distinct smaller elements of $A$. This is not `IsSumFree`, which only requires
$(A+A)\cap A=\emptyset$ (including the case $2a$).
-/
def IsSubsetSumFree (A : Set ℕ) : Prop :=
  ∀ s : Finset ℕ, 2 ≤ s.card → (s : Set ℕ) ⊆ A → s.sum id ∉ A

/-- The increasing enumeration of `A`, so `enum A 0` is the least element of `A`. -/
noncomputable def enum (A : Set ℕ) (n : ℕ) : ℕ := Nat.nth (· ∈ A) n

/--
Let $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ be an infinite sum-free set - that is, there are no
solutions to
$$
a=b_1+\cdots+b_r
$$
with $b_1<\cdots<b_r<a\in A$. How small can $a_{n+1}-a_n$ be?
-/
@[category research open, AMS 5 11]
theorem erdos_876.parts.i :
    sInf {α : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
        (enum A (n + 1) - enum A n : ℝ) < (n + 1 : ℝ) ^ (α + ε)} = answer(sorry) := by
  sorry

/--
Let $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ be an infinite sum-free set - that is, there are no
solutions to
$$
a=b_1+\cdots+b_r
$$
with $b_1<\cdots<b_r<a\in A$. Is it possible that $a_{n+1}-a_n<n$?
-/
@[category research open, AMS 5 11]
theorem erdos_876.parts.ii :
    answer(sorry) ↔
      ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
        ∀ n, enum A (n + 1) - enum A n < n + 1 := by
  sorry

/--
Erdős [Er62c] proved that a sum-free set has density zero.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.density_zero (A : Set ℕ) (hA : IsSubsetSumFree A) :
    A.HasDensity 0 := by
  sorry

/--
Deshouillers, Erdős, and Melfi [DEM99] constructed a sum-free set that grows like
$a_n\sim n^{3+o(1)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.dem99 :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      ∃ ε : ℕ → ℝ, ε =o[atTop] (1 : ℕ → ℝ) ∧
        Tendsto (fun n : ℕ => (enum A n : ℝ) / (n + 1 : ℝ) ^ (3 + ε (n + 1))) atTop (𝓝 1) := by
  sorry

/--
Erdős [Er98] writes that Graham 'recently proved' that there is such a sequence for which
$a_{n+1}-a_n<n^{1+o(1)}$, and that Melfi proved a somewhat weaker result.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.graham :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      ∃ ε : ℕ → ℝ, ε =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ n in atTop, (enum A (n + 1) - enum A n : ℝ) < (n + 1 : ℝ) ^ (1 + ε n) := by
  sorry

/--
Luczak and Schoen [LuSc00] have proved that, for all large $N$,
$$
\lvert A\cap [1,N]\rvert\ll (N\log N)^{1/2},
$$
for every such sum-free set $A$.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.luczak_schoen_upper (A : Set ℕ) (hA : IsSubsetSumFree A) :
    (fun N : ℕ => ((A ∩ Icc 1 N).ncard : ℝ)) =O[atTop]
      fun N => (N * log N) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Luczak and Schoen [LuSc00] proved that there exists a sum-free set $B$ such that
$$
\lvert B\cap [1,N]\rvert \gg \frac{N^{1/2}}{(\log N)^{1/2+o(1)}}
$$
for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.luczak_schoen_lower :
    ∃ B : Set ℕ, B.Infinite ∧ IsSubsetSumFree B ∧
      ∃ ε : ℕ → ℝ, ε =o[atTop] (1 : ℕ → ℝ) ∧
        (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2) / (log N) ^ ((1 : ℝ) / 2 + ε N)) =O[atTop]
          fun N => ((B ∩ Icc 1 N).ncard : ℝ) := by
  sorry

/--
In [Er75b] and [Er77c] Erdős asks to determine the maximum possible value of
$\sum_{n\in A}\frac{1}{n}$. Erdős had proved this is $<100$, and Sullivan had shown that this is
$<4$, and Sullivan conjectured the maximum is slightly larger than $2$.
-/
@[category research open, AMS 5 11]
theorem erdos_876.variants.reciprocal_sum :
    sSup {r : ℝ | ∃ A : Set ℕ, IsSubsetSumFree A ∧
      HasSum (fun n : A => (1 / (n : ℝ))) r} = answer(sorry) := by
  sorry

/--
Erdős had proved this is $<100$.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.reciprocal_sum_lt_100 (A : Set ℕ) (hA : IsSubsetSumFree A) :
    Summable (fun n : A => (1 / (n : ℝ))) ∧ ∑' n : A, (1 / (n : ℝ)) < 100 := by
  sorry

/--
Sullivan had shown that this is $<4$.
-/
@[category research solved, AMS 5 11]
theorem erdos_876.variants.reciprocal_sum_lt_4 (A : Set ℕ) (hA : IsSubsetSumFree A) :
    Summable (fun n : A => (1 / (n : ℝ))) ∧ ∑' n : A, (1 / (n : ℝ)) < 4 := by
  sorry

end Erdos876
