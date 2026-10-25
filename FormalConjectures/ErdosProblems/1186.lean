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
# Erdős Problem 1186

*References:*
- [erdosproblems.com/1186](https://www.erdosproblems.com/1186)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
- [PRS08] Parrilo, Pablo A. and Robertson, Aaron and Saracino, Dan, *On the asymptotic minimum
  number of monochromatic 3-term arithmetic progressions*. J. Combin. Theory Ser. A (2008),
  185-192. [arXiv:math/0609532](https://arxiv.org/abs/math/0609532)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1186

/--
`monoCount k n c` is the number of monochromatic $k$-term arithmetic progressions in
$\{1,\ldots,n\}$ under the $2$-colouring `c`. The progression $a, a+d, \ldots, a+(k-1)d$ with first
term $a$ and common difference $d \geq 1$ is the pair `(a, d)`, with $a \geq 1$ and
$a + (k-1)d \leq n$. Each progression is counted once.

This is the count of [Er80, p. 93]: there are $\sim n^2/(2(k-1))$ progressions, and the upper bound
in (7) there is their number times the probability $2^{1-k}$ that a random colouring makes one of
them monochromatic. The definition is meant for $k \geq 2$.
-/
def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

/--
`minMonoCount k n` is the least number of monochromatic $k$-term arithmetic progressions in a
$2$-colouring of $\{1,\ldots,n\}$. This is $A(n;k)$ in [Er80, p. 93]. The set of values contains
`monoCount k n (fun _ => true)`, so `sInf` is a true minimum.
-/
noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

/--
`δ k` is the largest constant $\delta_k$ such that every $2$-colouring of $\{1,\ldots,n\}$ has at
least $(\delta_k - o(1))n^2$ monochromatic $k$-term arithmetic progressions, that is,
$\liminf_{n\to\infty} A(n;k)/n^2$.

The quotient `minMonoCount k n / n ^ 2` lies in $[0,1]$, so this `liminf` is not a junk value.
Convergence of the quotient is not assumed. If it converges, `δ k` is its limit.
-/
noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

/-- Any $2$-colouring gives an upper bound for `minMonoCount`. -/
@[category API, AMS 5]
theorem minMonoCount_le (k n : ℕ) (c : ℕ → Bool) : minMonoCount k n ≤ monoCount k n c :=
  Nat.sInf_le ⟨c, rfl⟩

/-- In $\{1,\ldots,5\}$ the $3$-term progressions are $\{a,a+1,a+2\}$ for $a \in \{1,2,3\}$ and
$\{1,3,5\}$. -/
@[category test, AMS 5]
theorem monoCount_three_five : monoCount 3 5 (fun _ => true) = 4 := by
  decide

def erdos_1186.answer : ℕ → ℝ := sorry

/--
Let $\delta_k$ be such that in any $2$-colouring of $\{1,\ldots,n\}$ there exist at least
$(\delta_k+o(1))n^2$ many monochromatic $k$-term arithmetic progressions. Give reasonable bounds
(or even an asymptotic formula) for $\delta_k$.

We read "reasonable bounds" as determining the order of magnitude of $\delta_k$ as $k \to \infty$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_1186 : δ =Θ[atTop] erdos_1186.answer := by
  sorry

/--
Van der Waerden's theorem implies $\delta_k\gg_k 1$.

For fixed $k$ this says $\delta_k > 0$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1186.variants.van_der_waerden (k : ℕ) (hk : 2 ≤ k) : 0 < δ k := by
  sorry

/--
The probabilistic method implies
$$\delta_k \leq \frac{1}{(k-1)2^{k}}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_1186.variants.probabilistic (k : ℕ) (hk : 2 ≤ k) :
    δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
  sorry

/--
Parrilo, Robertson, and Saracino [PRS08] have proved
$$0.0511\approx \frac{1675}{32768}\leq \delta_3 \leq \frac{117}{2192}\approx 0.0533,$$
and conjectured the upper bound is correct.
-/
@[category research solved, AMS 5 11]
theorem erdos_1186.variants.prs_bounds : 1675 / 32768 ≤ δ 3 ∧ δ 3 ≤ 117 / 2192 := by
  sorry

/--
Parrilo, Robertson, and Saracino [PRS08] have proved
$$0.0511\approx \frac{1675}{32768}\leq \delta_3 \leq \frac{117}{2192}\approx 0.0533,$$
and conjectured the upper bound is correct.

This is the conjecture $\delta_3 = \frac{117}{2192}$.
-/
@[category research open, AMS 5 11]
theorem erdos_1186.variants.prs_conjecture : δ 3 = 117 / 2192 := by
  sorry

end Erdos1186
