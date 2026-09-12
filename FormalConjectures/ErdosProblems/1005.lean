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
# Erdős Problem 1005

*References:*
- [erdosproblems.com/1005](https://www.erdosproblems.com/1005)
- [Ci26] Cipollini, R., *A sharp 5/8 bound for an Erdős-Sós pairwise-sums problem*.
  arXiv:2606.29361 (2026).
- [Er43] Erdős, P., *A note on {F}arey series*. Quart. J. Math. Oxford Ser. (1943), 82--85.
- [Ma42] Mayer, A. E., *A mean value theorem concerning {F}arey series*. Quart. J. Math. Oxford
  Ser. (1942), 48--57.
- [vD25b] W. van Doorn, *Improved bounds for the Mayer-Erdős phenomenon on similarly ordered
  Farey fractions*. arXiv:2509.00121 (2025).
-/

open Filter Finset
open scoped Asymptotics Topology

namespace Erdos1005

/--
Two rationals are similarly ordered if the product of the differences of their numerators and of
their denominators is nonnegative.
-/
def SimilarlyOrdered (q r : ℚ) : Prop :=
  0 ≤ (q.num - r.num) * ((q.den : ℤ) - r.den)

/--
The Farey fractions of order `n`: the reduced fractions $a/b$ with $0 \leq a/b \leq 1$ and
$1 \leq b \leq n$.
-/
def fareySet (n : ℕ) : Finset ℚ :=
  ((Icc (0 : ℕ) n ×ˢ Icc 1 n).filter fun p => p.1 ≤ p.2 ∧ p.1.Coprime p.2).image
    fun p => (p.1 : ℚ) / p.2

/-- The Farey sequence of order `n`, listed in increasing order. -/
noncomputable def fareySeq (n : ℕ) : List ℚ :=
  (fareySet n).sort (· ≤ ·)

/--
`f n` is the largest integer such that if $k < l \leq k + f(n)$ are indices in the Farey sequence
of order $n$, then the corresponding fractions are similarly ordered.

The source defines $f(n)$ for $n \geq 4$, when the sequence contains a pair that is not similarly
ordered. For $n < 4$ every pair is similarly ordered, so the set of admissible windows is unbounded
and `sSup` on `ℕ` is `0`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m | ∀ (k l : ℕ) (hk : k < l) (hl : l < (fareySeq n).length),
    l ≤ k + m → SimilarlyOrdered ((fareySeq n)[k]'(hk.trans hl)) ((fareySeq n)[l]'hl)}

/--
Let $\frac{a_1}{b_1},\frac{a_2}{b_2},\ldots$ be the Farey fractions of order $n\geq 4$. Let $f(n)$
be the largest integer such that if $1\leq k<l\leq k+f(n)$ then $\frac{a_k}{b_k}$ and
$\frac{a_l}{b_l}$ are similarly ordered — in other words,
$$(a_k-a_l)(b_k-b_l)\geq 0.$$
Estimate $f(n)$ — in particular, is there a constant $c>0$ such that $f(n)=(c+o(1))n$ for all
large $n$?

The answer is yes: Cipollini and GPT 5.5 [Ci26] proved
$f(n)=\left(\frac{1}{4}+o(1)\right)n$.
-/
@[category research solved, AMS 11]
theorem erdos_1005 : answer(True) ↔
    ∃ c > (0 : ℝ), Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (nhds c) := by
  sorry

/--
The function $f(n)$ was first considered by Mayer [Ma42], who proved $f(n)\to \infty$ as
$n\to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.mayer : Tendsto f atTop atTop := by
  sorry

/--
Erdős [Er43] proved $f(n)\gg n$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.erdos : ∃ c > (0 : ℝ), ∀ᶠ n in atTop, c * n ≤ (f n : ℝ) := by
  sorry

/--
van Doorn [vD25b] proved
$$\left(\frac{1}{12}-o(1)\right)n\leq f(n).$$
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.vanDoorn_lower :
    ∃ o : ℕ → ℝ, o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ᶠ n in atTop, (1 / 12 - o n) * n ≤ (f n : ℝ) := by
  sorry

/--
van Doorn [vD25b] proved
$$f(n)\leq \frac{1}{4}n+O(1).$$
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.vanDoorn_upper :
    ∃ C : ℝ, ∀ n ≥ 4, (f n : ℝ) ≤ (1 / 4) * n + C := by
  sorry

/--
A corresponding lower bound was proved asymptotically by Cipollini and GPT 5.5 [Ci26], so that
$$f(n)=\left(\frac{1}{4}+o(1)\right)n.$$
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.quarter :
    Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (nhds (1 / 4)) := by
  sorry

end Erdos1005
