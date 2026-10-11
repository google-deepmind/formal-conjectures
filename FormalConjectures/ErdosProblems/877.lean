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
# Erdős Problem 877

*References:*
- [erdosproblems.com/877](https://www.erdosproblems.com/877)
- [CaEr90] Cameron, P. J. and Erdős, P., _On the number of sets of integers with various
  properties_. (1990), 61-79.
- [Er98] Erdős, Paul, _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [LuSc01] Łuczak, Tomasz and Schoen, Tomasz, _On the number of maximal sum-free sets_. Proc.
  Amer. Math. Soc. (2001), 2205--2207.
- [BLST15] Balogh, József and Liu, Hong and Sharifzadeh, Maryam and Treglown, Andrew, _The
  number of maximal sum-free subsets of integers_. Proc. Amer. Math. Soc. (2015), 4713--4721.
- [BLST18] Balogh, József and Liu, Hong and Sharifzadeh, Maryam and Treglown, Andrew, _Sharp
  bound on the number of maximal sum-free subsets of integers_. J. Eur. Math. Soc. (JEMS) (2018),
  1885--1911.
-/

@[expose] public section

open Filter Asymptotics Real

namespace Erdos877

/-- `A` is a maximal sum-free subset of `{1, …, n}`. -/
def IsMaximalSumFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsSumFree (A : Set ℕ) ∧
    ∀ B ⊆ Finset.Icc 1 n, IsSumFree (B : Set ℕ) → A ⊆ B → A = B

open scoped Classical in
/-- `fm n` counts the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$. -/
noncomputable def fm (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsMaximalSumFree n A).card

/--
Let $f_m(n)$ count the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$ - that is,
there are no solutions to $a=b+c$ in $A$ and $A$ is maximal with this property. Estimate $f(n)$
- is it true that $f_m(n)=o(2^{n/2})$?

A problem of Cameron and Erdős. Łuczak and Schoen [LuSc01] proved that there exists a constant
$c<1/2$ such that $f_m(n)<2^{cn}$, resolving this question. Balogh, Liu, Sharifzadeh, and
Treglown [BLST15] proved that $f_m(n)=2^{(\frac{1}{4}+o(1))n}$.

See [748](https://www.erdosproblems.com/748) for the non-maximal case.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos877.lean#L170"]
theorem erdos_877 : answer(True) ↔
    (fun n : ℕ ↦ (fm n : ℝ)) =o[atTop] fun n : ℕ ↦ (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

/-- Łuczak and Schoen [LuSc01] proved that there exists a constant $c<1/2$ such that
$f_m(n)<2^{cn}$ for all large $n$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos877.lean#L127"]
theorem erdos_877.variants.luczak_schoen :
    ∃ c : ℝ, c < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, (fm n : ℝ) ≤ 2 ^ (c * n) := by
  sorry

/-- Cameron and Erdős [CaEr90] proved that $f_m(n)>2^{n/4}$. -/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.cameron_erdos :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) / 4) < fm n := by
  sorry

/-- Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved that
$f_m(n)=2^{(\frac{1}{4}+o(1))n}$. -/
@[category research solved, AMS 5 11]
theorem erdos_877.variants.balogh_liu_sharifzadeh_treglown :
    Tendsto (fun n : ℕ ↦ logb 2 (fm n) / n) atTop (nhds (1 / 4)) := by
  sorry

end Erdos877
