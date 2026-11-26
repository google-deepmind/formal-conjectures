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
# The Irving–Leather conjecture on stable matchings

*References:*
- [Concerning the maximum number of stable matchings in the stable marriage problem](https://core.ac.uk/download/pdf/82220141.pdf)
  by E. G. Thurber, §2 and Appendix A.
- [A recurrence giving a lower bound for stable matchings](https://oeis.org/A005154/a005154.pdf)
  by Clay Thomas, Proposition 1.

Let $M(n)$ be the maximum number of stable matchings with $n$ participants per side and complete,
strict preferences. The Irving–Leather construction has $a_k$ stable matchings at size $2^k$.
-/

@[expose] public section

open Filter
open scoped Topology

namespace IrvingLeather

/-- The maximum number of stable matchings over all preference profiles of size $n$. -/
noncomputable def maxStableMatchings (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : StableMarriage.Profile n ↦ StableMarriage.numStableMatchings p)

/-- The number $a_k$ of stable matchings in the Irving–Leather construction of size $2^k$. -/
def irvingLeatherCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 3 * irvingLeatherCount (k + 1) ^ 2 - 2 * irvingLeatherCount k ^ 4

/--
Thurber's §2 attributes to Irving and Leather the conjecture that their construction attains
the maximum number of stable matchings at every power-of-two size.
-/
@[category research open, AMS 5]
theorem irving_leather_pow_two (k : ℕ) :
    maxStableMatchings (2 ^ k) = irvingLeatherCount k := by
  sorry

/--
A proposed weaker variant states that $M(n)^{1/n}$ and $a_k^{1/2^k}$ converge to the same real
number. Thomas's recurrence analysis gives approximately $2.280142$ for the second limit.
The first sequence is indexed by $n+1$ to start at positive sizes.
-/
@[category research open, AMS 5]
theorem irving_leather_growth_rate :
    ∃ c : ℝ,
      Tendsto (fun n : ℕ ↦ Real.rpow (maxStableMatchings (n + 1) : ℝ)
        (1 / ((n : ℝ) + 1))) atTop (𝓝 c) ∧
      Tendsto (fun k : ℕ ↦ Real.rpow (irvingLeatherCount k : ℝ)
        (1 / (2 : ℝ) ^ k)) atTop (𝓝 c) := by
  sorry

end IrvingLeather
