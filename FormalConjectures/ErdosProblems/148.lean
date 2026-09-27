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
# Erdős Problem 148

*References:*
- [erdosproblems.com/148](https://www.erdosproblems.com/148)
- [ElPl21] Elsholtz, Christian and Planitzer, Stefan, *Sums of four and more unit fractions and
  approximate parametrizations*. Bull. Lond. Math. Soc. (2021), 695-709.
- [Ko14] Konyagin, S. V., *Double exponential lower bound for the number of representations of
  unity by Egyptian fractions*. Math. Notes (2014), 277-281.
-/

@[expose] public section

open Filter Real

namespace Erdos148

/-- `F k` is the number of solutions to $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$ with
$1 \leq n_1 < \cdots < n_k$, that is, the number of $k$-element sets of positive integers whose
reciprocals sum to $1$. -/
noncomputable def F (k : ℕ) : ℕ :=
  {S : Finset ℕ | S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1}.ncard

/-- The sequence $u_0 = 1$, $u_{n+1} = u_n(u_n + 1)$ of [ElPl21, Corollary 3]:
$1, 2, 6, 42, 1806, \ldots$, a shifted copy of Sylvester's sequence. This is the sequence
`Erdos315.u` of Erdős Problem 315. -/
def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

/-- The constant $c_0 = \lim_{n \to \infty} u_n^{2^{-n}} = 1.5979102\ldots$ of
[ElPl21, Corollary 3]. The sequence $u_n^{2^{-n}}$ is increasing and bounded by $2$
[ElPl21, Remark 3], so the limit is its supremum. This constant is the square of the Vardi
constant $1.26408\ldots$, which is `Erdos315.c₀`. -/
noncomputable def c₀ : ℝ := ⨆ n : ℕ, (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)

/-- The only representation of $1$ as a single unit fraction is $1 = \frac{1}{1}$. -/
@[category test, AMS 11]
theorem F_one : F 1 = 1 := by
  have h : {S : Finset ℕ | S.card = 1 ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1} =
      {{1}} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.card_eq_one]
    constructor
    · rintro ⟨⟨a, rfl⟩, -, hsum⟩
      simp only [Finset.sum_singleton, one_div, inv_eq_one, Nat.cast_eq_one] at hsum
      rw [hsum]
    · rintro rfl
      exact ⟨⟨1, rfl⟩, by simp, by simp⟩
  rw [F, h, Set.ncard_singleton]

/-- The fifth term of the sequence is $u_4 = 1806$. -/
@[category test, AMS 11]
theorem u_four : u 4 = 1806 := by
  decide

/--
Let $F(k)$ be the number of solutions to
$$ 1= \frac{1}{n_1}+\cdots+\frac{1}{n_k},$$
where $1\leq n_1<\cdots<n_k$ are distinct integers. Find good estimates for $F(k)$.
-/
@[category research open, AMS 11]
theorem erdos_148 : (fun k ↦ (F k : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
The current best bounds known are
$$2^{c^{\frac{k}{\log k}}}\leq F(k) \leq c_0^{(\frac{1}{5}+o(1))2^k},$$
where $c>0$ is some absolute constant and $c_0=1.5979102\ldots$ is the square of the 'Vardi
constant' $1.26408\cdots$. The lower bound is due to Konyagin [Ko14] and the upper bound to
Elsholtz and Planitzer [ElPl21]. (erdosproblems.com gives $c_0=1.26408\cdots$;
[ElPl21, Corollary 3] has $c_0=1.5979102\ldots$.)

[Ko14, Theorem 1] states the lower bound in the explicit form
$$F(k) \geq \exp\left(\exp\left(\left(\frac{(\log 2)(\log 3)}{3}+o(1)\right)
\frac{k}{\log k}\right)\right) \quad (k \to \infty),$$
which is the statement formalised here.
-/
@[category research solved, AMS 11]
theorem erdos_148.variants.lower_bound :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ k : ℕ in atTop,
      exp (exp ((log 2 * log 3 / 3 + o k) * ((k : ℝ) / log k))) ≤ F k := by
  sorry

/--
The current best bounds known are
$$2^{c^{\frac{k}{\log k}}}\leq F(k) \leq c_0^{(\frac{1}{5}+o(1))2^k},$$
where $c>0$ is some absolute constant and $c_0=1.5979102\ldots$ is the square of the 'Vardi
constant' $1.26408\cdots$. The lower bound is due to Konyagin [Ko14] and the upper bound to
Elsholtz and Planitzer [ElPl21]. (erdosproblems.com gives $c_0=1.26408\cdots$;
[ElPl21, Corollary 3] has $c_0=1.5979102\ldots$.)

[ElPl21, Corollary 3(2)] shows that for every $\varepsilon > 0$ and all $k \geq k(\varepsilon)$,
the number $f_k(1,1) \geq F(k)$ of solutions with $n_1 \leq \cdots \leq n_k$ is less than
$c_0^{(\frac{2}{5}+\varepsilon)2^{k-1}} = c_0^{(\frac{1}{5}+\frac{\varepsilon}{2})2^k}$.
-/
@[category research solved, AMS 11]
theorem erdos_148.variants.upper_bound :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ k : ℕ in atTop,
      (F k : ℝ) ≤ c₀ ^ ((1 / 5 + o k) * 2 ^ k) := by
  sorry

end Erdos148
