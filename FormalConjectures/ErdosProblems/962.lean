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
# Erdős Problem 962

*References:*
- [erdosproblems.com/962](https://www.erdosproblems.com/962)
- [Er65] Erdős, P., Extremal problems in number theory. Proc. Sympos. Pure Math., Vol. VIII (1965), 181-189.
- [Er76e] Erdős, P., Problems and results on consecutive integers. Publ. Math. Debrecen (1976), 271-282.
- [Tang](https://github.com/QuanyuTang/erdos-problem-962/blob/main/On_Erd%C5%91s_Problem_962.pdf)
- [Tao](https://www.erdosproblems.com/forum/thread/962)
-/

open Classical Filter Real

namespace Erdos962

/--
`Erdos962Prop n k` : there exists $m \le n$ such that each of
$m+1, \ldots, m+k$ has a prime divisor strictly larger than $k$.
-/
def Erdos962Prop (n k : ℕ) : Prop :=
  ∃ m ≤ n, ∀ i ∈ Set.Icc 1 k,
    ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ (m + i)

/--
Let $k(n)$ be the maximal $k$ such that there exists $m \le n$ with
$m+1, \ldots, m+k$ each divisible by a prime $> k$.
-/
noncomputable def k (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => Erdos962Prop n k) n

/--
Main conjecture:

$\log k(n) \le (\log n)^{(1/2 + o(1))}$
-/
@[category research open, AMS 11]
theorem erdos_962 :
    answer(sorry) ↔
      ∃ ε : ℕ → ℝ,
        (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧
        ∀ᶠ n : ℕ in atTop,
          log (k n : ℝ)
            ≤ rpow (log n) ((1 : ℝ) / 2 + ε n) := by
  sorry

/--
Tang's lower bound [Tang]:

$\log k(n) \ge (1/\sqrt{2} - o(1)) * \sqrt{\log n * \log \log n}$
-/
@[category research solved, AMS 11]
theorem erdos_962.variants.tang_lower_bound :
    ∃ ε : ℕ → ℝ,
      (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧
      ∀ᶠ n : ℕ in atTop,
          (1 / sqrt 2 - ε n) *
              sqrt (log n * log (log n))
            ≤ log (k n : ℝ) := by
  sorry

/--
Tao's upper bound [Tao]:

$k(n) \le (1 + o(1)) * n^{1/2}$
-/
@[category research solved, AMS 11]
theorem erdos_962.variants.tao_upper_bound :
    ∃ ε : ℕ → ℝ,
      (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧
      ∀ᶠ n : ℕ in atTop,
          (k n : ℝ) ≤ (1 + ε n) * sqrt n := by
  sorry

end Erdos962
