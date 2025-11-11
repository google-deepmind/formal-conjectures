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
# Erdős Problem 1055

*Reference:* [erdosproblems.com/1055](https://www.erdosproblems.com/1055)
-/

namespace Erdos1055

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.-/
def IsOfClass : ℕ+ → ℕ → Prop := fun r ↦
  PNat.caseStrongInductionOn (p := fun (_ : ℕ+) ↦ ℕ → Prop) r
    (fun p ↦ (p + 1).primeFactors ⊆ {2, 3})
    (fun n H p ↦
      (∀ r ∈ (p + 1).primeFactors,
        ∃ (m : ℕ+) (hm : m ≤ n), H m hm r) ∧
      (∃ r ∈ (p + 1).primeFactors,
        ∀ (m : ℕ+) (hm : m ≤ n), H m hm r → m = n))

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.
Show that for each $r$ there exists a prime $p$ of class $r$. -/
@[category undergraduate, AMS 11]
theorem exists_p (r : ℕ+) : ∃ p, p.Prime ∧ IsOfClass r p :=
  sorry

open Classical

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.
Let $p_r$ is the least prime in class $r$.-/
noncomputable def p (r : ℕ+) : ℕ := Nat.find (exists_p r)

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.
Are there infinitely many primes in each class?-/
@[category research open, AMS 11]
theorem erdos_1055 (r) : {p | p.Prime ∧ IsOfClass r p}.Infinite :=
  sorry

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.
If $p_r$ is the least prime in class $r$, then how does $p_r^{1/r}$ behave?
Erdos conjectured that this tends to infinity. -/
@[category research open, AMS 11]
theorem erdos_1055.variants.erdos_limit :
    Filter.atTop.Tendsto (fun r ↦ (p r : ℝ) ^ (1 / r : ℝ)) Filter.atTop :=
  sorry

/-- A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are
$2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor
of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.
If $p_r$ is the least prime in class $r$, then how does $p_r^{1/r}$ behave?
Selfridge conjectured that this is bounded. -/
@[category research open, AMS 11]
theorem erdos_1055.variants.selfridge_limit :
    ∃ M, ∀ r, (p r : ℝ) ^ (1 / r : ℝ) ≤ M :=
  sorry

--TODO(Paul-Lez): formalize the rest of the problems on the page.

end Erdos1055
