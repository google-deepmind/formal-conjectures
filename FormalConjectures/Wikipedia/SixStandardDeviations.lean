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
# Six standard deviations suffice (Spencer's theorem)

Spencer's theorem in discrepancy theory: for every $n$ and every family of $n$ subsets
$S_1, \dots, S_n$ of $\{1, \dots, n\}$, there is a colouring
$\chi : \{1, \dots, n\} \to \{-1, +1\}$ such that
$$\left|\sum_{j \in S_i} \chi(j)\right| \le 6\sqrt{n}$$
for every $i$.

A uniformly random colouring only achieves the bound $O(\sqrt{n \log n})$, so Spencer's
theorem ("six standard deviations suffice") is a genuine improvement over the basic
probabilistic method; its proof uses a partial-colouring argument based on the entropy
method, and the bound $\Theta(\sqrt{n})$ is tight up to the value of the constant.
Spencer's original argument is non-constructive; polynomial-time algorithms achieving
$O(\sqrt{n})$ were later found by Bansal (2010) and Lovett–Meka (2012).

The Komlós conjecture (the subject of a companion file in this directory) would
strengthen this theorem: applied to the incidence vectors of the sets, scaled by
$1/\sqrt{n}$, it would give a discrepancy bound $O(\sqrt{n})$ for any number of sets,
not just $n$ of them.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Discrepancy_of_hypergraphs#General_hypergraphs)
- [J. Spencer, *Six standard deviations suffice*,
  Trans. Amer. Math. Soc. **289** (1985), 679–706](https://doi.org/10.1090/S0002-9947-1985-0784009-0)
- [N. Bansal, *Constructive algorithms for discrepancy minimization*,
  FOCS 2010, 3–10](https://doi.org/10.1109/FOCS.2010.7)
- [S. Lovett and R. Meka, *Constructive discrepancy minimization by walking on the edges*,
  SIAM J. Comput. **44** (2015), 1573–1582](https://doi.org/10.1137/130929400)
-/

namespace SixStandardDeviations

/--
**Six standard deviations suffice** (Spencer, 1985)

For every $n$ and every family of $n$ subsets $S_1, \dots, S_n$ of $\{1, \dots, n\}$,
there is a colouring $\chi : \{1, \dots, n\} \to \{-1, +1\}$ such that
$\left|\sum_{j \in S_i} \chi(j)\right| \le 6\sqrt{n}$ for every $i$.
-/
@[category research solved, AMS 5]
theorem six_standard_deviations :
    ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
        ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n := by
  sorry

/--
**The random colouring bound**

There is a constant $K > 0$ such that for every $n$ and every family of $n$ subsets
$S_1, \dots, S_n$ of $\{1, \dots, n\}$, there is a colouring
$\chi : \{1, \dots, n\} \to \{-1, +1\}$ with
$\left|\sum_{j \in S_i} \chi(j)\right| \le K \sqrt{n \log(n + 2)}$ for every $i$.
This follows from a Chernoff bound applied to a uniformly random colouring, and is
the benchmark that Spencer's theorem improves upon by removing the logarithmic
factor. (The shift $n + 2$ inside the logarithm is a harmless normalization keeping
it positive for $n \in \{0, 1\}$.)
-/
@[category research solved, AMS 5]
theorem six_standard_deviations.variants.random_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
        ∀ i, |∑ j ∈ S i, χ j| ≤ K * Real.sqrt (n * Real.log (n + 2)) := by
  sorry

/--
Sanity check: with no points and no sets ($n = 0$), the empty colouring works and
the bound $6\sqrt{0} = 0$ holds vacuously.
-/
@[category test, AMS 5]
theorem six_standard_deviations.variants.zero_sets (S : Fin 0 → Finset (Fin 0)) :
    ∃ χ : Fin 0 → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt 0 :=
  ⟨Fin.elim0, fun j => j.elim0, fun i => i.elim0⟩

end SixStandardDeviations
