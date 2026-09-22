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
# Erdős Problem 542

*References:*
- [erdosproblems.com/542](https://www.erdosproblems.com/542)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [Er98] Erdős, Paul, _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [ScSz59] Schinzel, A. and Szekeres, G., _Sur un problème de M. Paul Erdős_. Acta Sci. Math.
  (Szeged) (1959), 221-229.
- [Ch96] Chen, Yong-Gao, _On a problem of P. Erdős_. Acta Sci. Math. (Szeged) (1996), 101--114.
-/

@[expose] public section

open Filter Real

namespace Erdos542

/-- A set `A ⊆ {1, …, n}` such that `lcm(a, b) > n` for all distinct `a, b ∈ A`. -/
def IsLcmFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b

/-- The integers `m ≤ n` which do not divide any element of `A`. -/
def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m ↦ ∀ a ∈ A, ¬ a ∣ m

/--
Is it true that if $A\subseteq\{1,\ldots,n\}$ is a set such that $[a,b]>n$ for all $a\neq b$,
where $[a,b]$ is the least common multiple, then
$$\sum_{a\in A}\frac{1}{a}\leq \frac{31}{30}?$$

The answer is yes, proved by Schinzel and Szekeres [ScSz59]. The bound is best possible as
$A=\{2,3,5\}$ demonstrates.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos542.lean#L2114"]
theorem erdos_542.parts.i : answer(True) ↔
    ∀ (n : ℕ) (A : Finset ℕ), IsLcmFree n A → ∑ a ∈ A, (1 : ℝ) / a ≤ 31 / 30 := by
  sorry

/-- The bound $31/30$ is attained by $A=\{2,3,5\}$ (with $n=5$). -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos542.lean#L2114"]
theorem erdos_542.variants.sharp :
    IsLcmFree 5 {2, 3, 5} ∧ ∑ a ∈ ({2, 3, 5} : Finset ℕ), (1 : ℝ) / a = 31 / 30 := by
  sorry

/--
Is it true that if $A\subseteq\{1,\ldots,n\}$ is a set such that $[a,b]>n$ for all $a\neq b$,
then there must be $\gg n$ many $m\leq n$ which do not divide any $a\in A$?

The answer is no, proved by Schinzel and Szekeres [ScSz59].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos542.lean#L2114"]
theorem erdos_542.parts.ii : answer(False) ↔
    ∃ c > 0, ∀ (n : ℕ) (A : Finset ℕ), IsLcmFree n A →
      c * n ≤ ((uncovered n A).card : ℝ) := by
  sorry

/--
Schinzel and Szekeres [ScSz59] proved that, for any $\epsilon>0$, there are sets $A$ as in
the problem with $o(n)$ many uncovered $m\leq n$ and for which
$\sum_{a\in A}\frac{1}{a}>1-\epsilon$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos542.lean#L2114"]
theorem erdos_542.variants.schinzel_szekeres :
    ∀ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (A : Finset ℕ), IsLcmFree n A ∧
      ((uncovered n A).card : ℝ) ≤ δ * n ∧ 1 - ε < ∑ a ∈ A, (1 : ℝ) / a := by
  sorry

/--
Schinzel and Szekeres [ScSz59] proved that there are examples with at most $n/(\log n)^c$
many such $m$, for some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_542.variants.log_power : ∃ c > 0, ∃ᶠ n : ℕ in atTop, ∃ A : Finset ℕ,
    IsLcmFree n A ∧ ((uncovered n A).card : ℝ) ≤ n / (log n) ^ c := by
  sorry

/--
Chen [Ch96] has proved that if $n>172509$ then
$$\sum_{a\in A}\frac{1}{a}< \frac{1}{3}+\frac{1}{4}+\frac{1}{5}+\frac{1}{7}+\frac{1}{11}.$$
-/
@[category research solved, AMS 11]
theorem erdos_542.variants.chen (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A) :
    ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11 := by
  sorry

/--
In [Er73] Erdős further speculates that in fact
$$\sum_{a\in A}\frac{1}{a}\leq 1+o(1),$$
where the $o(1)$ term $\to 0$ as $n\to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_542.variants.one_add_little_o : answer(sorry) ↔
    ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
      ∀ (n : ℕ) (A : Finset ℕ), IsLcmFree n A → ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n := by
  sorry

/--
In [Er98] Erdős mentions that he, Schinzel, and Szekeres conjectured that $2,3,5$ and
$3,4,5,7,11$ are the only two sequences for which the sum is $>1$.
-/
@[category research open, AMS 11]
theorem erdos_542.variants.only_two : answer(sorry) ↔
    ∀ (n : ℕ) (A : Finset ℕ), IsLcmFree n A → 1 < ∑ a ∈ A, (1 : ℝ) / a →
      A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11} := by
  sorry

end Erdos542
