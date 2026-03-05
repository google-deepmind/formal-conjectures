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
# Erdős Problem 451

*Reference:* [erdosproblems.com/451](https://www.erdosproblems.com/451)

Estimate $n_k$, the smallest integer $> 2k$ such that $\prod_{1 \le i \le k} (n_k - i)$
has no prime factor in $(k, 2k)$.

Erdős and Graham proved $n_k > k^{1+c}$ for some constant $c > 0$.
Erdős conjectures that $n_k > k^d$ for all constant $d$, and $n_k < e^{o(k)}$.

[Er79d] Erdős, P., _Some unconventional problems in number theory_.
Math. Mag. **52** (1979), 67-70.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Classical

namespace Erdos451

/-- The product $(n-1)(n-2)\cdots(n-k)$ has no prime factor $p$ with $k < p < 2k$. -/
def noInteriorPrimeFactor (k n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → k < p → p < 2 * k →
    ¬(p ∣ ∏ i ∈ Finset.Icc 1 k, (n - i))

/-- $n_k$: the smallest integer $> 2k$ such that the product $(n-1)(n-2)\cdots(n-k)$
has no prime factor in $(k, 2k)$. Returns $0$ if no such integer exists. -/
noncomputable def erdos451_nk (k : ℕ) : ℕ :=
  if h : ∃ n, 2 * k < n ∧ noInteriorPrimeFactor k n
  then Nat.find h
  else 0

/--
Erdős Problem 451 [Er79d][ErGr80, p.89]:

$n_k$ grows superpolynomially but subexponentially:
1. For all $d > 0$, $n_k > k^d$ for all sufficiently large $k$.
2. For all $\varepsilon > 0$, $n_k < e^{\varepsilon \cdot k}$ for all sufficiently large $k$.
-/
@[category research open, AMS 11]
theorem erdos_451 :
    (∀ d : ℝ, 0 < d → ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (k : ℝ) ^ d < (erdos451_nk k : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (erdos451_nk k : ℝ) < Real.exp (ε * (k : ℝ))) := by
  sorry

end Erdos451
