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
# Erdős Problem 877

*References:*
- [erdosproblems.com/877](https://www.erdosproblems.com/877)
- [BLST15] Balogh, József and Liu, Hong and Sharifzadeh, Maryam and Treglown, Andrew, *The number of
  maximal sum-free subsets of integers*. Proc. Amer. Math. Soc. (2015), 4713--4721.
- [BLST18] Balogh, József and Liu, Hong and Sharifzadeh, Maryam and Treglown, Andrew, *Sharp bound on
  the number of maximal sum-free subsets of integers*. J. Eur. Math. Soc. (JEMS) (2018), 1885--1911.
- [LuSc01] Łuczak, Tomasz and Schoen, Tomasz, *On the number of maximal sum-free sets*. Proc. Amer.
  Math. Soc. (2001), 2205--2207.
-/

open Finset Filter

namespace Erdos877

/--
`A` is a maximal sum-free subset of `{1, …, n}`: it is contained in `{1, …, n}`, is sum-free in the
sense of `IsSumFree` (no solutions to $a=b+c$ in $A$), and cannot be extended by any further element
of `{1, …, n}` while remaining sum-free.

This is not the subset-sum-free condition of Erdős Problem 876, which forbids writing an element of
$A$ as a sum of two or more distinct smaller elements of $A$.
-/
def IsMaximalSumFreeIn (A : Set ℕ) (n : ℕ) : Prop :=
  A ⊆ Set.Icc 1 n ∧ IsSumFree A ∧
    ∀ ⦃x : ℕ⦄, x ∈ Set.Icc 1 n → x ∉ A → ¬ IsSumFree (A ∪ {x})

/--
$f(n)$, the number of (not necessarily maximal) sum-free subsets of $\{1,\ldots,n\}$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  {A : Finset ℕ | A ⊆ Icc 1 n ∧ IsSumFree (A : Set ℕ)}.ncard

/--
$f_m(n)$, the number of maximal sum-free subsets of $\{1,\ldots,n\}$.
-/
noncomputable def f_m (n : ℕ) : ℕ :=
  {A : Finset ℕ | A ⊆ Icc 1 n ∧ IsMaximalSumFreeIn (A : Set ℕ) n}.ncard

/--
Let $f_m(n)$ count the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$ - that is, there
are no solutions to $a=b+c$ in $A$ and $A$ is maximal with this property. Estimate $f(n)$ - is it
true that $f_m(n)=o(2^{n/2})$?

A problem of Cameron and Erdős, who proved that $f_m(n)>2^{n/4}$, and also asked whether
$$f_m(n)=o(f(n)),$$
where $f(n)$ counts the number of all (not necessarily maximal) sum-free sets. Luczak and Schoen
[LuSc01] proved that there exists a constant $c<1/2$ such that
$$f_m(n)<2^{cn},$$
resolving these questions. Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved that
$$f_m(n)=2^{(\frac{1}{4}+o(1))n},$$
which the same authors [BLST18] later improved to
$$f_m(n)=(C_n+o(1))2^{n/4},$$
where $C_n$ is some explicit constant depending only on $n\pmod{4}$.

See [748](https://www.erdosproblems.com/748) for the non-maximal case.
-/
@[category research solved, AMS 5 11]
theorem erdos_877 : answer(True) ↔
    (fun n : ℕ => (f_m n : ℝ)) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) := by
  sorry

/--
A problem of Cameron and Erdős, who also asked whether
$$f_m(n)=o(f(n)),$$
where $f(n)$ counts the number of all (not necessarily maximal) sum-free sets. Luczak and Schoen
[LuSc01] proved that there exists a constant $c<1/2$ such that
$$f_m(n)<2^{cn},$$
resolving these questions.
-/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.o_of_all :
    (fun n : ℕ => (f_m n : ℝ)) =o[atTop] (fun n : ℕ => (f n : ℝ)) := by
  sorry

/--
Cameron and Erdős proved that $f_m(n)>2^{n/4}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.cameron_erdos :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) / 4) < (f_m n : ℝ) := by
  sorry

/--
Luczak and Schoen [LuSc01] proved that there exists a constant $c<1/2$ such that
$$f_m(n)<2^{cn},$$
resolving these questions.
-/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.luczak_schoen :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop, (f_m n : ℝ) < (2 : ℝ) ^ (c * (n : ℝ)) := by
  sorry

/--
Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved that
$$f_m(n)=2^{(\frac{1}{4}+o(1))n}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.blst15 :
    ∃ ε : ℕ → ℝ, ε =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop,
        (f_m n : ℝ) = (2 : ℝ) ^ (((1 : ℝ) / 4 + ε n) * (n : ℝ)) := by
  sorry

/--
The same authors [BLST18] later improved to
$$f_m(n)=(C_n+o(1))2^{n/4},$$
where $C_n$ is some explicit constant depending only on $n\pmod{4}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.blst18 :
    ∃ C : ZMod 4 → ℝ,
      (fun n : ℕ => (f_m n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 4) - C n) =o[atTop]
        (1 : ℕ → ℝ) := by
  sorry

end Erdos877
