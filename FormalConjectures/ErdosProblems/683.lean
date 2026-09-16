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

import FormalConjectures.ErdosProblems.«961»

/-!
# Erdős Problem 683

*References:*
- [erdosproblems.com/683](https://www.erdosproblems.com/683)
- [Er34] Erdős, Paul, A Theorem of Sylvester and Schur. J. London Math. Soc. (1934), 282--288.
- [Er55d] Erdős, P., On consecutive integers. Nieuw Arch. Wisk. (3) (1955), 124--128.
- [Er79d] Erdős, P., Some unconventional problems in number theory. Acta Math. Acad. Sci. Hungar. (1979), 71-80.
-/

namespace Erdos683

open Filter Real Erdos961

/--
Let $P(n, k)$ be the largest prime factor of $\binom{n}{k}$.
-/
def P (n k : ℕ) : ℕ := (n.choose k).primeFactors.sup id

/--
Let $P(n, k)$ be the largest prime factor of $\binom{n}{k}$.
There exists $c > 0$ such that $P(n, k) \ge \min(n - k + 1, k^{1 + c})$ for all $0 < k \le n/2$.

Erdős stated this for $1 \le k \le n$ with the bound $\min(n-k+1, k^{1+c})$ [Er79d]. The
minimum is needed even for $k \le n/2$: at $n = 2k$ every prime factor of $\binom{2k}{k}$ is at
most $2k$, so $P(n, k) \ge k^{1+c}$ fails for large $k$. The range $k \le n/2$ is natural
(cf. [#961](https://www.erdosproblems.com/961) and the
[discussion](https://www.erdosproblems.com/forum/discuss/683)).
-/
@[category research open, AMS 11]
theorem erdos_683 : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 →
      (P n k : ℝ) ≥ min (↑(n - k + 1) : ℝ) ((k : ℝ) ^ (1 + c)) := by
  sorry

/--
Sylvester and Schur [Er34] proved that $P(n, k) > k$ for $k \le n/2$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.sylvester_schur :
    ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > k := by
  sorry

/--
Erdős [Er55d] improved this to $P(n, k) \gg \min(n - k + 1, k \log k)$ for $k \le n/2$. The
minimum cannot be dropped: at $n = 2k$ one has $P(n, k) \le 2k$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.erdos_log :
    ∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 →
      (P n k : ℝ) ≥ min (↑(n - k + 1) : ℝ) (c * k * Real.log k) := by
  sorry

/--
Standard heuristics suggest that $P(n, k) > \min(n - k + 1, e^{c\sqrt{k}})$ for some constant
$c > 0$.
-/
@[category research open, AMS 11]
theorem erdos_683.variant.exp_sqrt :
    ∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 →
      (P n k : ℝ) > min (↑(n - k + 1) : ℝ) (Real.exp (c * Real.sqrt k)) := by
  sorry

-- TODO: Erdos 683 and 961 are equivalent.

end Erdos683
