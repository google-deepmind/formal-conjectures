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
public import FormalConjectures.ErdosProblems.«711»

/-!
# Erdős Problem 710

*References:*
- [erdosproblems.com/710](https://www.erdosproblems.com/710)
- [ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to $n$ with distinct
  multiples in another interval*. Nederl. Akad. Wetensch. Indag. Math. 42 (1980), 147-161.
  [PDF](https://www.renyi.hu/~p_erdos/1980-13.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos710

/-- $f(n)$: the least $L$ such that the open interval $(n,n+L)$ contains distinct integers
$a_1,\ldots,a_n$ with $k \mid a_k$ for all $1 \leq k \leq n$. This is
`Erdos711.HasDivisibleDistinctTuple n n L`.

The set of such $L$ is nonempty for every $n$ (take $a_k = k(n+1)$ and $L = n^2+1$), so `sInf`
is the true minimum. For $n = 0$ there is nothing to choose and $f(0) = 0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {L : ℕ | Erdos711.HasDivisibleDistinctTuple n n L}

/-- Any admissible interval length is an upper bound for $f(n)$. -/
@[category API, AMS 11]
theorem f_le {n L : ℕ} (h : Erdos711.HasDivisibleDistinctTuple n n L) : f n ≤ L :=
  Nat.sInf_le h

/-- The tuple $a_k = k(n+1)$ shows that the set defining $f(n)$ is nonempty. -/
@[category API, AMS 11]
theorem hasDivisibleDistinctTuple_sq (n : ℕ) :
    Erdos711.HasDivisibleDistinctTuple n n (n ^ 2 + 1) := by
  refine ⟨fun i ↦ (i.val + 1) * (n + 1), fun i j hij ↦ ?_, fun i ↦ ⟨?_, ?_, ?_⟩⟩
  · have hij' : (i.val + 1) * (n + 1) = (j.val + 1) * (n + 1) := hij
    have := mul_right_cancel₀ (by omega : n + 1 ≠ 0) hij'
    exact Fin.ext (by omega)
  · show n < (i.val + 1) * (n + 1)
    nlinarith [Nat.zero_le (i.val * n)]
  · show (i.val + 1) * (n + 1) < n + (n ^ 2 + 1)
    have := Nat.mul_le_mul_right (n + 1) (show i.val + 1 ≤ n from i.isLt)
    nlinarith
  · exact dvd_mul_right _ _

/-- The example $11, 22, 21, 16, 15, 12, 14, 24, 18, 20$ of [ErPo80, p. 147] shows $f(10) \leq 15$.
[ErPo80] use the interval $(n, f(n)]$, where this reads $f(10) = 24$. -/
@[category test, AMS 11]
theorem f_ten_le : f 10 ≤ 15 :=
  f_le ⟨![11, 22, 21, 16, 15, 12, 14, 24, 18, 20], by decide, by decide⟩

def erdos_710.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be minimal such that in $(n,n+f(n))$ there exist distinct integers $a_1,\ldots,a_n$
such that $k\mid a_k$ for all $1\leq k\leq n$. Obtain an asymptotic formula for $f(n)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_710 : (fun n ↦ (f n : ℝ)) ~[atTop] erdos_710.answer := by
  sorry

/--
Erdős and Pomerance [ErPo80] proved
$$\left(\frac{2}{\sqrt{e}}+o(1)\right)n\left(\frac{\log n}{\log\log n}\right)^{1/2}
\leq f(n) \leq (1.7398\cdots+o(1))n(\log n)^{1/2}.$$

This is the lower bound [ErPo80, Theorem 2].
-/
@[category research solved, AMS 11]
theorem erdos_710.variants.lower_bound :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (2 / Real.sqrt (Real.exp 1) - ε) * n *
        Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (f n : ℝ) := by
  sorry

/--
Erdős and Pomerance [ErPo80] proved
$$\left(\frac{2}{\sqrt{e}}+o(1)\right)n\left(\frac{\log n}{\log\log n}\right)^{1/2}
\leq f(n) \leq (1.7398\cdots+o(1))n(\log n)^{1/2}.$$

This is the upper bound. Here $1.7398\cdots = \sqrt{r}/(1-r)$, where $r$ is the solution of
$e^{-r} = r$ [ErPo80, (11), p. 154].
-/
@[category research solved, AMS 11]
theorem erdos_710.variants.upper_bound :
    ∃ r : ℝ, Real.exp (-r) = r ∧ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ (Real.sqrt r / (1 - r) + ε) * n * Real.sqrt (Real.log n) := by
  sorry

end Erdos710
