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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 609

*Reference:* [erdosproblems.com/609](https://www.erdosproblems.com/609)

Let $f(n)$ be the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured
with $n$ colours then there must be a monochromatic odd cycle of length at most $m$.
Estimate $f(n)$.

A problem of Erdős and Graham [ErGr75]. The edges of $K_{2^n}$ can be
$n$-coloured to avoid monochromatic odd cycles entirely (partition vertices by
binary coordinates). Day and Johnson [DaJo17] proved $f(n) \to \infty$ and
$f(n) \geq 2^{c\sqrt{\log n}}$ for some $c > 0$. Janzer and Yip [JaYi25] proved
$f(n) \leq O(n^{3/2} \cdot 2^{n/2})$.

[ErGr75] Erdős, P. and Graham, R.

[DaJo17] Day, A. N. and Johnson, J. R.

[JaYi25] Janzer, O. and Yip, C. H.
-/

namespace Erdos609

/-- There exists a monochromatic cycle of length $k$ in an edge coloring of $K_N$.
A cycle is an injective sequence of $k \geq 3$ vertices $v_0, \ldots, v_{k-1}$ where all
consecutive edges $v_0 v_1, v_1 v_2, \ldots, v_{k-1} v_0$ have the same color. -/
def HasMonoCycle609 {N c : ℕ} (χ : Fin N → Fin N → Fin c) (k : ℕ) : Prop :=
  k ≥ 3 ∧
  ∃ (v : Fin k → Fin N),
    Function.Injective v ∧
    ∃ col : Fin c, ∀ i : Fin k,
      χ (v i) (v ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩) = col

/--
**Erdős Problem 609** [ErGr75]:

For every $n \geq 1$, every symmetric $n$-coloring of the edges of $K_{2^n+1}$
contains a monochromatic odd cycle. (This establishes that $f(n)$ is finite.)
-/
@[category research solved, AMS 5]
theorem erdos_609 :
    ∀ n : ℕ, n ≥ 1 →
    ∀ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
      (∀ u v, χ u v = χ v u) →
      ∃ k, Odd k ∧ HasMonoCycle609 χ k := by
  sorry

/--
**Erdős Problem 609** (Day–Johnson lower bound) [DaJo17]:

There exists $c > 0$ such that for all sufficiently large $n$, there exists a
symmetric $n$-coloring of $K_{2^n+1}$ with no monochromatic odd cycle of length
less than $2^{c \cdot \sqrt{\log n}}$.
-/
@[category research solved, AMS 5]
theorem erdos_609.variants.lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∃ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
        (∀ u v, χ u v = χ v u) ∧
        ∀ k, Odd k → HasMonoCycle609 χ k →
          (k : ℝ) ≥ (2 : ℝ) ^ (c * Real.sqrt (Real.log (n : ℝ))) := by
  sorry

/--
**Erdős Problem 609** (Janzer–Yip upper bound) [JaYi25]:

There exists $C > 0$ such that for all sufficiently large $n$, every symmetric
$n$-coloring of $K_{2^n+1}$ contains a monochromatic odd cycle of length at most
$C \cdot n^{3/2} \cdot 2^{n/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_609.variants.upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
        (∀ u v, χ u v = χ v u) →
        ∃ k, Odd k ∧ HasMonoCycle609 χ k ∧
          (k : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

end Erdos609
