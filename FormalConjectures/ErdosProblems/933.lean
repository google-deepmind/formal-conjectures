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
# Erdős Problem 933

*References:*
- [erdosproblems.com/933](https://www.erdosproblems.com/933)
- [Er76d] Erdős, P, Problems and results on number theoretic properties of consecutive integers and
  related questions. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics (Univ.
  Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
-/

open Filter

namespace Erdos933

/-- The 2-adic valuation of $n(n+1)$. -/
def k (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

/-- The 3-adic valuation of $n(n+1)$. -/
def l (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

/--
If $n(n+1)=2^k3^lm$, where $(m,6)=1$, then is it true that
$\limsup_{n\to \infty} \frac{2^k3^l}{n\log n}=\infty$?
-/
@[category research open, AMS 11]
theorem erdos_933 :
    answer(sorry) ↔
      atTop.limsup (fun n : ℕ ↦
        ((((2 ^ k n * 3 ^ l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal)) = ⊤ := by
  sorry

/--
Mahler proved (a more general result that implies in particular) that $2^k3^l<n^{1+o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_933.variants.mahler :
    ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧
      ∀ᶠ n in atTop, ((2 ^ k n * 3 ^ l n : ℕ) : ℝ) < (n : ℝ) ^ (1 + c n) := by
  sorry

/--
Erdős [Er76d] wrote 'it is easy to see' that for infinitely many $n$, $2^k 3^l > n\log n$.

Steinerberger has noted a simple proof of this fact follows from taking $n=2^{3^r}$ for any
integer $r\geq 1$, when $k=3^r$ and $l=r+1$.
-/
@[category research solved, AMS 11]
theorem erdos_933.variants.lower_bound :
    Set.Infinite { n : ℕ | ((2 ^ k n * 3 ^ l n : ℕ) : ℝ) > (n : ℝ) * Real.log (n : ℝ) } := by
  sorry

end Erdos933
