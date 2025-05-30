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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 304
*Reference:* [erdosproblems.com/304](https://www.erdosproblems.com/304)
-/

open Asymptotics Filter

/-- Let $$N(a, b)$$, denoted here by `smallestCollection a b` be the minimal k such that there
exist integers $1 < n_1 < n_2 < ... < n_k$ with
$$\frac{a}{b} = \sum_{i=1}^k \frac{1}{n_i}$$ -/
noncomputable def smallestCollection (a b : ℕ) : ℕ :=
  sInf {k | ∃ s : Finset ℕ, s.card = k ∧ (∀ n ∈ s, n > 1) ∧
            (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

/-- Write $$N(b) = max_{1 \leq a < b} N(a, b)$$. -/
noncomputable def smallestCollectionTo (b : ℕ) : ℕ :=
  sSup {smallestCollection a b | a ∈ Finset.Ico 1 b}

/--
In 1950, Erdős [Er50c] proved the upper bound $$N(b) \ll \log b / \log \log b$$.
[Er50c] Erdős, P., Az ${1}/{x_1} + {1}/{x_2} + \ldots + {1}/{x_n} =A/B$ egyenlet eg\'{E}sz sz\'{A}m\'{u} megold\'{A}sairól. Mat. Lapok (1950), 192-210.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.upper_1950 :
    (fun b => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => Real.log b / Real.log (Real.log b)) := by
  sorry

/--
In 1950, Erdős [Er50c] proved the lower bound $$\log \log b \ll N(b)$$.
[Er50c] Erdős, P., Az ${1}/{x_1} + {1}/{x_2} + \ldots + {1}/{x_n} =A/B$ egyenlet eg\'{E}sz sz\'{A}m\'{u} megold\'{A}sairól. Mat. Lapok (1950), 192-210.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.lower_1950 :
    (fun b : ℕ => Real.log (Real.log b)) =O[atTop]
      (fun b => (smallestCollectionTo b : ℝ)) := by
  sorry

/--
In 1985 Vose [Vo85] proved the upper bound $$N(b) \ll \sqrt{\log b}$$.
[Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.upper_1985 :
    (fun b => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => Real.sqrt (Real.log b)) :=
  sorry

/--
Is it true that $$N(b) \ll \log \log b$$?
-/
@[category research open, AMS 11]
theorem upper_bound :
    (fun b : ℕ => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b : ℕ => Real.log (Real.log b)) ↔ answer(sorry) := by
  sorry
