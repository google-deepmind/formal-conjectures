/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 283

*References:*
- [erdosproblems.com/283](https://www.erdosproblems.com/283)
- [Al19] Alekseyev, Max A., On partitions into squares of distinct integers whose
reciprocals sum to 1. (2019), 213--221.
- [Ca60] Cassels, J. W. S., On the representation of integers as the sums of distinct summands taken from a fixed set. Acta Sci. Math. (Szeged) (1960), 111-124.
- [Gr63] Graham, R. L., A theorem on partitions. J. Austral. Math. Soc. (1963), 435-441.
- [vD25] W. van Doorn, Partitions with prescribed sum of rationals: asymptotic bounds. arXiv:2502.02200 (2025).
-/

open Filter Polynomial Finset

namespace Erdos283

/--
Given a polynomial `p`, the predicate that if the leading coefficient is positive and
there exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$, then for all sufficiently large $m$,
there exist integers $1≤n_1<\dots < n_k$ such that $$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
and $$m=p(n_1)+\cdots+p(n_k)$$?
-/
def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
  ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  m = ∑ i ∈ Finset.Icc 1 (Fin.last k),  p.eval (n i)

/--
Let $p\colon \mathbb{Z} \rightarrow \mathbb{Z}$ be a polynomial whose leading coefficient is
positive and such that there exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$. Is it true that,
for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
and
$$m=p(n_1)+\cdots+p(n_k)$$?

GPT 5.5 Pro (prompted by Price) has given a proof that the answer is yes, for the stronger version
with $1$ replaced by any rational $\alpha>0$.

This was formalized in Lean by Ammanamanchi using Opus 4.6 and GPT 5.5 Pro.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at "https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P283/Proof_flat.lean"]
theorem erdos_283 : answer(True) ↔ ∀ p : ℤ[X], Condition p := by
  sorry

/--
Graham [Gr63] has proved this when $p(x)=x$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.graham : Condition X := by
  sorry

/--
Graham also conjectures that this remains true with $1$ replaced by an arbitrary rational $\alpha>0$
(provided $m$ is taken sufficiently large depending on $\alpha$).
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.graham_alpha :
  ∀ (p : ℤ[X]) (α : ℚ),
    0 < p.leadingCoeff →
    (¬ ∃ (d : ℤ), d ≥ 2 ∧ ∀ (n : ℤ), n ≥ 1 → d ∣ p.eval n) →
    α > 0 →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
        (∑ n ∈ S, (1 / (n : ℚ))) = α ∧
        (∑ n ∈ S, p.eval (n : ℤ)) = (m : ℤ) := by
  sorry

/--
Cassels [Ca60] has proved that these conditions on the polynomial imply every sufficiently large
integer is the sum of $p(n_i)$ with distinct $n_i$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.cassels :
  ∀ (p : ℤ[X]),
    0 < p.leadingCoeff →
    (¬ ∃ (d : ℤ), d ≥ 2 ∧ ∀ (n : ℤ), n ≥ 1 → d ∣ p.eval n) →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
        (∑ n ∈ S, p.eval (n : ℤ)) = (m : ℤ) := by
  sorry

/--
Burr has proved this if $p(x)=x^k$ with $k\geq 1$ and if we allow $n_i=n_j$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.burr :
  ∀ (k : ℕ), k ≥ 1 →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ M : Multiset ℕ, (∀ n ∈ M, 1 ≤ n) ∧
        (M.map (fun n ↦ 1 / (n : ℚ))).sum = 1 ∧
        (M.map (fun n ↦ (n : ℤ)^k)).sum = (m : ℤ) := by
  sorry

/--
Alekseyev [Al19] has proved this when $p(x)=x^2$, for all $m>8542$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.alekseyev :
  ∀ (m : ℕ), m > 8542 →
    ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
      (∑ n ∈ S, (1 / (n : ℚ))) = 1 ∧
      (∑ n ∈ S, (n : ℤ)^2) = (m : ℤ) := by
  sorry

/--
van Doorn [vD25] has investigated the question of what 'sufficiently large' means for $p(x)=x$.
van Doorn has also proved the original conjecture for many linear and quadratic polynomials.
For example, if $p(x) = x + b$ with $1 \leq b \leq 5000$, then the conjecture is true.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.van_doorn_linear :
  ∀ b : ℤ, 1 ≤ b → b ≤ 5000 → Condition (X + C b) := by
  sorry

/--
van Doorn [vD25] has proved the original conjecture for many linear and quadratic polynomials.
For example, if $p(x) = x^2 + b$ with $1 \leq b \leq 800$, then the conjecture is true.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.van_doorn_quadratic :
  ∀ b : ℤ, 1 ≤ b → b ≤ 800 → Condition (X^2 + C b) := by
  sorry

end Erdos283
