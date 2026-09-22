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
# Erdős Problem 748

*References:*
- [erdosproblems.com/748](https://www.erdosproblems.com/748)
- [CaEr90] Cameron, P. J. and Erdős, P., _On the number of sets of integers with various
  properties_. (1990), 61-79.
- [Er94b] Erdős, Paul, _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261-269.
- [Er98] Erdős, Paul, _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [Gr04] Green, Ben, _The Cameron-Erdős conjecture_. Bull. London Math. Soc. (2004), 769-778.
- [Sa03] Sapozhenko, A. A., _The Cameron-Erdős conjecture_. Dokl. Akad. Nauk (2003), 749-752.
-/

@[expose] public section

open Filter Real

namespace Erdos748

open scoped Classical in
/-- `f n` counts the number of sum-free $A\subseteq \{1,\ldots,n\}$, i.e. $A$ contains no
solutions to $a=b+c$ with $a,b,c\in A$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)).card

/--
Let $f(n)$ count the number of sum-free $A\subseteq \{1,\ldots,n\}$, i.e. $A$ contains no
solutions to $a=b+c$ with $a,b,c\in A$. Is it true that
$$f(n)=2^{(1+o(1))\frac{n}{2}}?$$

The Cameron–Erdős conjecture. This is true, and in fact $f(n) \ll 2^{n/2}$, which was proved
independently by Green [Gr04] and Sapozhenko [Sa03].

The statement $f(n)=2^{(1+o(1))n/2}$ is formalised as $\log_2 f(n)/n\to 1/2$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos748.lean#L1228"]
theorem erdos_748 : answer(True) ↔
    Tendsto (fun n : ℕ ↦ logb 2 (f n) / n) atTop (nhds (1 / 2)) := by
  sorry

/-- It is trivial to see that $f(n) \geq 2^{\frac{n}{2}}$, considering all subsets of
$[n/2,n]$. -/
@[category textbook, AMS 5 11]
theorem erdos_748.variants.lower_bound (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (f n : ℝ) := by
  sorry

/-- Green [Gr04] and Sapozhenko [Sa03] proved that $f(n) \ll 2^{n/2}$. -/
@[category research solved, AMS 5 11]
theorem erdos_748.variants.green_sapozhenko :
    ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2) := by
  sorry

/-- In fact, both Green [Gr04] and Sapozhenko [Sa03] prove the stronger asymptotic
$f(n) \sim c_n 2^{n/2}$, where $c_n$ takes on one of two values depending on the parity of
$n$. -/
@[category research solved, AMS 5 11]
theorem erdos_748.variants.asymptotic :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      Tendsto (fun m : ℕ ↦ (f (2 * m) : ℝ) / 2 ^ m) atTop (nhds c₀) ∧
      Tendsto (fun m : ℕ ↦ (f (2 * m + 1) : ℝ) / 2 ^ ((2 * m + 1 : ℝ) / 2)) atTop
        (nhds c₁) := by
  sorry

end Erdos748
