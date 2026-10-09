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
# Erdős Problem 768

*References:*
- [erdosproblems.com/768](https://www.erdosproblems.com/768)
- [Er74b] Erdős, P., *Remarks on some problems in number theory*.
  Math. Balkanica (1974), 197–202.
-/

namespace Erdos768

open Filter Asymptotics

/-- The defining property of $A$: for every prime $p \mid n$, there is some $d \mid n$ with
$d>1$ and $d \equiv 1 \pmod p$. -/
def HasErdos768Property (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → ∃ d, d ∣ n ∧ 1 < d ∧ d % p = 1

/-- The counting function $\lvert A \cap [1,N]\rvert$. -/
noncomputable def erdos768Count (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter HasErdos768Property).card

/-- The normalized density $\lvert A \cap [1,N]\rvert/N$. -/
noncomputable def erdos768Density (N : ℕ) : ℝ :=
  (erdos768Count N : ℝ) / (N : ℝ)

/-- The scale $\sqrt{\log N}\log\log N$ appearing in the conjecture. -/
noncomputable def erdos768Scale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))

/-- Let $A \subset \mathbb{N}$ be the set of $n$ such that for every prime $p \mid n$ there is
some $d \mid n$ with $d>1$ and $d \equiv 1 \pmod p$. Is there a constant $c>0$ such that,
for all large $N$,
$$\frac{\lvert A\cap[1,N]\rvert}{N}=
\exp\big(-(c+o(1))\sqrt{\log N}\log\log N\big)?$$ -/
@[category research open, AMS 11]
theorem erdos_768 : answer(sorry) ↔ ∃ c > 0, ∃ error : ℕ → ℝ,
    error =o[atTop] (fun _ ↦ (1 : ℝ)) ∧ ∀ᶠ N in atTop,
      erdos768Density N = Real.exp (-(c + error N) * erdos768Scale N) := by
  sorry

end Erdos768
