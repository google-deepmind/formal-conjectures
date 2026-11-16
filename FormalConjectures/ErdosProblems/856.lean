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
# Erdős Problem 856

*References:*
- [erdosproblems.com/856](https://www.erdosproblems.com/856)
- [Er70] Erdős, P., *Some extremal problems in combinatorial number theory*. Mathematical Essays
  Dedicated to A. J. Macintyre (1970), 123-133. [PDF](https://www.renyi.hu/~p_erdos/1970-21.pdf)
- [TaZh25b] Tang, Q. and Zhang, S., *Harmonic LCM patterns and sunflower-free capacity*.
  [arXiv:2512.20055](https://arxiv.org/abs/2512.20055) (2025).

The problem is closely related to the sunflower problem
[erdosproblems.com/857](https://www.erdosproblems.com/857). The version with natural density in
place of the harmonic sum is [erdosproblems.com/536](https://www.erdosproblems.com/536).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos856

/-- A finite set `A` of natural numbers contains `k` distinct elements with the same pairwise least
common multiple: there is a subset `S ⊆ A` of size `k` and a number `L` such that
`lcm a b = L` for all distinct `a, b ∈ S`. -/
def HasEqualLcmTuple (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.card = k ∧ ∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- $f_k(N)$ is the maximum of $\sum_{n \in A} 1/n$ over all $A \subseteq \{1, \ldots, N\}$ that
contain no `k` distinct elements with the same pairwise least common multiple.

The set of values is finite and contains `0` (for `A = ∅`) when `k ≥ 1`, so the `sSup` is a
maximum. -/
noncomputable def f (k N : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ¬ HasEqualLcmTuple k A ∧
    s = ∑ n ∈ A, (n : ℝ)⁻¹}

/-- Every `A ⊆ {1, …, N}` without `k` distinct elements with the same pairwise least common
multiple has harmonic sum at most `f k N`. -/
@[category API, AMS 11]
theorem sum_le_f {k N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hfree : ¬ HasEqualLcmTuple k A) : ∑ n ∈ A, (n : ℝ)⁻¹ ≤ f k N := by
  have hfin : {s : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ¬ HasEqualLcmTuple k A ∧
      s = ∑ n ∈ A, (n : ℝ)⁻¹}.Finite := by
    refine ((Finset.Icc 1 N).powerset.finite_toSet.image
      (fun A : Finset ℕ => ∑ n ∈ A, (n : ℝ)⁻¹)).subset ?_
    rintro s ⟨B, hB, -, rfl⟩
    exact ⟨B, Finset.mem_coe.2 (Finset.mem_powerset.2 hB), rfl⟩
  exact le_csSup hfin.bddAbove ⟨A, hA, hfree, rfl⟩

/-- The numbers $6$, $10$, $15$ have the same pairwise least common multiple $30$. -/
@[category test, AMS 11]
theorem hasEqualLcmTuple_six_ten_fifteen : HasEqualLcmTuple 3 {6, 10, 15} :=
  ⟨{6, 10, 15}, Finset.Subset.refl _, by decide, 30, by decide⟩

def erdos_856.answer : ℕ → ℕ → ℝ := sorry

/--
Let $k\geq 3$ and $f_k(N)$ be the maximum value of $\sum_{n\in A}\frac{1}{n}$, where $A$ ranges
over all subsets of $\{1,\ldots,N\}$ which contain no subset of size $k$ with the same pairwise
least common multiple.

Estimate $f_k(N)$.

This is the question of Erdős [Er70, p. 127]. We read "estimate" as
$f_k(N) = \Theta(\text{answer})$ as $N \to \infty$, for each fixed $k$.
-/
@[category research open, question value, AMS 11]
theorem erdos_856 (k : ℕ) (hk : 3 ≤ k) :
    f k =Θ[atTop] erdos_856.answer k := by
  sorry

/--
Erdős [Er70, p. 127] notes that
$$f_k(N) \ll \frac{\log N}{\log\log N}.$$

The implied constant depends on $k$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.erdos_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, f k N ≤ C * (Real.log N / Real.log (Real.log N)) := by
  sorry

/-- The exponent $c_k = \frac{k-2}{e\,((k-2)!)^{1/(k-2)}}$ of [TaZh25b, Theorem 1.2] (called $b_k$
on the problem page, where $c_k$ denotes the upper exponent). -/
noncomputable def tangZhangExponent (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / (Real.exp 1 * ((Nat.factorial (k - 2) : ℕ) : ℝ) ^ (1 / ((k : ℝ) - 2)))

/--
Tang and Zhang [TaZh25b, Theorem 1.2] proved that, for fixed $k\geq 3$ and as $N\to\infty$,
$$f_k(N) \geq (\log N)^{c_k - o(1)}, \qquad c_k = \frac{k-2}{e\,((k-2)!)^{1/(k-2)}}.$$

The $o(1)$ is stated with an arbitrary $\varepsilon > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.tang_zhang_lower (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ (tangZhangExponent k - ε) ≤ f k N := by
  sorry

/--
Tang and Zhang [TaZh25b, Corollary 1.7] proved, as $N\to\infty$,
$$(\log N)^{\log(1.551)-o(1)}\leq f_3(N)\ll(\log N)^{\frac{3}{2^{2/3}}-1+o(1)}.$$

This is the lower bound, with the $o(1)$ stated with an arbitrary $\varepsilon > 0$. Since
$\log(1.551) = 0.4389\ldots$, it implies the site's $(\log N)^{0.438}\leq f_3(N)$ for large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.tang_zhang_three_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ (Real.log 1.551 - ε) ≤ f 3 N := by
  sorry

/--
Tang and Zhang [TaZh25b, Corollary 1.7] proved, as $N\to\infty$,
$$(\log N)^{\log(1.551)-o(1)}\leq f_3(N)\ll(\log N)^{\frac{3}{2^{2/3}}-1+o(1)}.$$

This is the upper bound, with the $o(1)$ and the implied constant absorbed into an arbitrary
$\varepsilon > 0$. The site rounds the exponent to $0.889$, but $\frac{3}{2^{2/3}}-1=0.8898\ldots$.
-/
@[category research solved, AMS 11]
theorem erdos_856.variants.tang_zhang_three_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, f 3 N ≤ Real.log N ^ (3 / (2 : ℝ) ^ ((2 : ℝ) / 3) - 1 + ε) := by
  sorry

end Erdos856
