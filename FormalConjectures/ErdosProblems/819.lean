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
# Erdős Problem 819

*References:*
- [erdosproblems.com/819](https://www.erdosproblems.com/819)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196-205.
-/

@[expose] public section

open Filter Asymptotics
open scoped Finset Pointwise

namespace Erdos819

/-- $f(N)$ is the maximum of $\lvert (A + A) \cap [1, N] \rvert$ over all
$A \subseteq \{1, \ldots, N\}$ with $\lvert A \rvert = \lfloor N^{1/2} \rfloor$, where
$\lfloor N^{1/2} \rfloor$ is `Nat.sqrt N`. Such sets exist for every $N$, since
$\lfloor N^{1/2} \rfloor \leq N$, so the maximum is over a nonempty family. -/
def f (N : ℕ) : ℕ :=
  (Finset.powersetCard (Nat.sqrt N) (Finset.Icc 1 N)).sup
    fun A ↦ #((A + A) ∩ Finset.Icc 1 N)

/-- Trivial upper bound: $f(N) \leq N$. -/
@[category API, AMS 5 11]
theorem f_le (N : ℕ) : f N ≤ N := by
  refine Finset.sup_le fun A _ ↦ ?_
  calc #((A + A) ∩ Finset.Icc 1 N) ≤ #(Finset.Icc 1 N) :=
        Finset.card_le_card Finset.inter_subset_right
    _ = N := by simp

def erdos_819.answer : ℕ → ℝ := sorry

/--
Let $f(N)$ be maximal such that there exists $A\subseteq \{1,\ldots,N\}$ with
$\lvert A\rvert=\lfloor N^{1/2}\rfloor$ such that $\lvert (A+A)\cap [1,N]\rvert=f(N)$.
Estimate $f(N)$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_819 : (fun N ↦ (f N : ℝ)) ~[atTop] erdos_819.answer := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{3}{8}-o(1)\right)N \leq f(N) \leq \left(\frac{1}{2}+o(1)\right)N.$$

This is the lower bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_819.variants.erdos_freud_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (3 / 8 - ε) * N ≤ (f N : ℝ) := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{3}{8}-o(1)\right)N \leq f(N) \leq \left(\frac{1}{2}+o(1)\right)N.$$

This is the upper bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_819.variants.erdos_freud_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (1 / 2 + ε) * N := by
  sorry

end Erdos819
