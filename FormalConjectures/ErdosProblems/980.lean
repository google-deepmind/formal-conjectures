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
# Erdős Problem 980

*Reference:* [erdosproblems.com/980](https://www.erdosproblems.com/980)

Let $k \geq 2$ and $n_k(p)$ denote the least $k$th power nonresidue of $p$.
Is it true that
$$\sum_{p < x} n_k(p) \sim c_k \cdot \frac{x}{\log x}$$
for some constant $c_k > 0$?

Proved by Erdős [Er61e] for $k = 2$, with $c_2 = \sum_{j=1}^{\infty} p_j / 2^j$.
The general case was proved by Elliott [El67b].

[Er65b] Erdős, P., _Extremal problems in number theory_. Lectures on Modern Mathematics,
Vol. III (1965), 196–244.

[Er61e] Erdős, P., _Remarks on number theory. I_. Mat. Lapok (1961), 10–17.

[El67b] Elliott, P.D.T.A., _A problem of Erdős concerning power residue sums_.
Acta Arith. (1967/68), 131–149.
-/

open Real

namespace Erdos980

/-- $a$ is a $k$th power residue modulo $p$ if there exists $b$ with $b^k \equiv a \pmod{p}$. -/
def IsKthPowerResidue (k p a : ℕ) : Prop :=
  ∃ b : ℕ, b ^ k % p = a % p

/-- The least $k$th power nonresidue of $p$: the smallest positive integer
that is not a $k$th power residue modulo $p$. Returns $0$ if no such number exists. -/
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  sInf {a : ℕ | 0 < a ∧ ¬IsKthPowerResidue k p a}

/--
Erdős Problem 980 [Er65b]:

For every $k \geq 2$, there exists a constant $c_k > 0$ such that
$$\sum_{\substack{p < x \\ p \text{ prime}}} n_k(p) \sim c_k \cdot \frac{x}{\log x}.$$

Formulated as: there exists $c_k > 0$ such that for every $\varepsilon > 0$, there exists $X_0$
such that for all $x \geq X_0$,
$$\left|\sum_{\substack{p < x \\ p \text{ prime}}} n_k(p) - c_k \cdot \frac{x}{\log x}\right|
\leq \varepsilon \cdot \frac{x}{\log x}.$$
-/
@[category research solved, AMS 11]
theorem erdos_980 : answer(True) ↔
    ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      |((Finset.filter (fun p => Nat.Prime p) (Finset.range x)).sum
          (fun p => (leastKthPowerNonresidue k p : ℝ))) -
        c * (x : ℝ) / log (x : ℝ)| ≤
      ε * (x : ℝ) / log (x : ℝ) := by
  sorry

end Erdos980
