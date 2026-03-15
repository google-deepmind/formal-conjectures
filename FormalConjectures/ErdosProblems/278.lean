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
# Erdős Problem 278

*Reference:* [erdosproblems.com/278](https://www.erdosproblems.com/278)

Let $A = \{n_1, \ldots, n_r\}$ be a finite set of positive integers. For any choice of
residues $a_1, \ldots, a_r$, consider the set of integers covered by the union of
congruence classes $m \equiv a_i \pmod{n_i}$. The covering density is the natural density
of this set (which exists since the covered set is periodic with period $\operatorname{lcm}(A)$).

Open question (Erdős–Graham [ErGr80, p.28]): What is the maximum covering density
achievable by a suitable choice of the $a_i$?

Settled (Simpson [Si86]): The minimum covering density is achieved when all $a_i$
are equal, and equals the inclusion-exclusion sum
$$\sum_i \frac{1}{n_i} - \sum_{i<j} \frac{1}{\operatorname{lcm}(n_i,n_j)}
  + \sum_{i<j<k} \frac{1}{\operatorname{lcm}(n_i,n_j,n_k)} - \cdots$$

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathématique (1980).

[Si86] Simpson, R. J., *Exact coverings of the integers by arithmetic progressions*.
Discrete Mathematics 59 (1986), 181–190.
-/

open scoped Classical

namespace Erdos278

/-- The covering density of congruences $m \equiv \text{offsets}(n) \pmod{n}$ for
$n \in \text{moduli}$. Since the covered set is periodic with period
$L = \operatorname{lcm}(\text{moduli})$, the density equals
$|\{m \in \{0,\ldots,L-1\} :
\exists n \in \text{moduli},\, n \mid (m - \text{offsets}(n))\}| / L$. -/
noncomputable def coveringDensity (moduli : Finset ℕ) (offsets : ℕ → ℤ) : ℚ :=
  let L := moduli.lcm id
  let covered := (Finset.range L).filter fun (m : ℕ) =>
    ∃ n ∈ moduli, (n : ℤ) ∣ ((m : ℤ) - offsets n)
  (covered.card : ℚ) / (L : ℚ)

/-- The inclusion-exclusion density for a set of moduli: the alternating sum
$\sum_{\emptyset \neq S \subseteq \text{moduli}} (-1)^{|S|+1} / \operatorname{lcm}(S)$.
This equals the covering density when all offsets are equal. -/
noncomputable def inclusionExclusionDensity (moduli : Finset ℕ) : ℚ :=
  ((moduli.powerset.filter fun S => S.Nonempty).sum fun S =>
    (-1 : ℚ) ^ (S.card + 1) / ((S.lcm id : ℕ) : ℚ))

/--
Erdős Problem 278 (Simpson's theorem [Si86]):

Is the minimum covering density, over all choices of offsets for a finite set of
positive integer moduli, achieved when all offsets are equal (giving the
inclusion-exclusion density)?

Answered affirmatively by Simpson [Si86].
-/
@[category research solved, AMS 11]
theorem erdos_278 : answer(True) ↔
    ∀ (moduli : Finset ℕ), (∀ n ∈ moduli, 0 < n) →
      (∀ offsets : ℕ → ℤ,
        inclusionExclusionDensity moduli ≤
          coveringDensity moduli offsets) ∧
      (∀ a : ℤ,
        coveringDensity moduli (fun _ => a) =
          inclusionExclusionDensity moduli) := by
  sorry

/-- Open question (Erdős–Graham [ErGr80, p.28]): What is the maximum
covering density achievable by a suitable choice of offsets? -/
@[category research open, AMS 11]
theorem erdos_278.variants.max_density
    (moduli : Finset ℕ) (h : ∀ n ∈ moduli, 0 < n) :
    IsGreatest {coveringDensity moduli offsets |
      offsets : ℕ → ℤ} (answer(sorry)) := by
  sorry

end Erdos278
