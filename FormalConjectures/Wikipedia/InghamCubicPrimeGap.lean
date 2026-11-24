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
# Primes Between Consecutive Cubes and Ingham's Prime-Gap Bound

Building on earlier sublinear prime-gap bounds of Hoheisel (1930), Heilbronn (1933), and Chudakov
(1936), Albert E. Ingham (1937) established $p_{n+1} - p_n = O_\varepsilon(p_n^{5/8 + \varepsilon})$
for every $\varepsilon > 0$. Because $5/8 < 2/3$, this implies that $(n^3, (n + 1)^3)$ contains a
prime for every large integer $n$—made explicit by Dudek (2016) for $n \ge \exp(\exp(33.217))$.
Whether a prime lies strictly between $n^3$ and $(n + 1)^3$ for every $n \ge 1$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Legendre%27s_conjecture#Partial_results)
- [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap#Upper_bounds)
- [Wikipedia: Albert Ingham](https://en.wikipedia.org/wiki/Albert_Ingham)
- A. E. Ingham, *On the difference between consecutive primes*, Quart. J. Math. Oxford Ser. **8**
  (1937), 255–266.
- A. W. Dudek, *An explicit result for primes between cubes*, Funct. Approx. Comment. Math. **55**
  (2016), no. 2, 177–197.
-/

@[expose] public section

open Filter

namespace InghamCubicPrimeGap

/-- Checks $(n^3, (n + 1)^3)$ for $1 \le n \le 10$ via explicit prime witnesses. -/
@[category test, AMS 11]
theorem exists_prime_between_cubes_up_to_ten (n : ℕ) (hn1 : 1 ≤ n) (hn10 : n ≤ 10) :
    ∃ p ∈ Set.Ioo (n ^ 3) ((n + 1) ^ 3), p.Prime := by
  interval_cases n
  · exact ⟨2, ⟨by norm_num, by norm_num⟩, by decide⟩
  · exact ⟨11, ⟨by norm_num, by norm_num⟩, by decide⟩
  · exact ⟨29, ⟨by norm_num, by norm_num⟩, by decide⟩
  · exact ⟨67, ⟨by norm_num, by norm_num⟩, by decide⟩
  · exact ⟨127, ⟨by norm_num, by norm_num⟩, by decide⟩
  · exact ⟨223, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨347, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨521, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨733, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨1009, ⟨by norm_num, by norm_num⟩, by norm_num⟩

/--
Cubic analogue of Legendre's conjecture: for every integer $n \ge 1$, the open interval
$(n^3, (n + 1)^3)$ contains a prime.
-/
@[category research open, AMS 11]
theorem prime_between_consecutive_cubes_for_all_pos (n : ℕ) (hn : 1 ≤ n) :
    ∃ p ∈ Set.Ioo (n ^ 3) ((n + 1) ^ 3), p.Prime := by
  sorry

/--
Ingham's prime-gap bound (1937): for each $\varepsilon > 0$, eventually
$p_{n+1} - p_n < p_n^{5/8 + \varepsilon}$.
-/
@[category research solved, AMS 11]
theorem ingham_five_eighths_prime_gap_theorem (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (primeGap n : ℝ) < (Nat.nth Nat.Prime n : ℝ) ^ ((5 : ℝ) / 8 + ε) := by
  sorry

/--
Ingham's cubic corollary (1937): for every sufficiently large $n \in \mathbb{N}$, the interval
$(n^3, (n + 1)^3)$ contains a prime.
-/
@[category research solved, AMS 11]
theorem prime_between_consecutive_cubes_for_all_pos.variants.eventually :
    ∀ᶠ n : ℕ in atTop, ∃ p ∈ Set.Ioo (n ^ 3) ((n + 1) ^ 3), p.Prime := by
  sorry

end InghamCubicPrimeGap
