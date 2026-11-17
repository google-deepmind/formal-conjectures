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
# Hemiperfect Numbers of Large Odd Index

Given odd $k \ge 1$, an integer $n > 0$ is termed $k$-hemiperfect when its divisor-sum ratio equals
$\frac{\sigma_1(n)}{n} = \frac{k}{2}$, equivalently $2 \sigma_1(n) = k n$. Since $\sigma_1(n) \ge n$
for $n \ge 1$, no $1$-hemiperfect integer exists. Minimal $k$-hemiperfect values (`OEIS A088912`)
start with $2$ ($k = 3$), $24$ ($k = 5$), $4320$ ($k = 7$), and $8910720$ ($k = 9$); exact minima
are established through $k = 15$, and Michel Marcus constructed examples at $k = 17$.

No $19$-hemiperfect integer has been found, leaving open whether any $19$-hemiperfect integer
exists and whether `OEIS A088912` extends to every odd index $k \ge 3$.

*References:*
- [Wikipedia: Hemiperfect number](https://en.wikipedia.org/wiki/Hemiperfect_number)
- [OEIS A159907](https://oeis.org/A159907)
- [OEIS A088912](https://oeis.org/A088912)
-/

@[expose] public section

namespace HemiperfectNumber

open scoped ArithmeticFunction.sigma

/-- An integer $n > 0$ is $k$-hemiperfect when $k$ is odd and $2 \sigma_1(n) = k n$. -/
def IsHemiperfect (k n : ℕ) : Prop :=
  Odd k ∧ 0 < n ∧ 2 * σ 1 n = k * n

/-- $2$ is $3$-hemiperfect ($2 \sigma_1(2) = 6 = 3 \cdot 2$), and $24$ is $5$-hemiperfect
($2 \sigma_1(24) = 120 = 5 \cdot 24$). -/
@[category test, AMS 11]
theorem isHemiperfect_small_examples : IsHemiperfect 3 2 ∧ IsHemiperfect 5 24 := by
  unfold IsHemiperfect
  decide

/-- Excludes $n = 0$, $n = 1$ at $k = 3$, and even index $k = 4$ at $n = 6$. -/
@[category test, AMS 11]
theorem not_isHemiperfect_boundary :
    ¬ IsHemiperfect 3 0 ∧ ¬ IsHemiperfect 3 1 ∧ ¬ IsHemiperfect 4 6 := by
  unfold IsHemiperfect
  decide

/-- No $1$-hemiperfect integer exists (since $2 \sigma_1(n) \ge 2 n > n$ for $n \ge 1$), and every
hemiperfect integer is even. -/
@[category API, AMS 11]
theorem not_isHemiperfect_one_and_even (n : ℕ) :
    ¬ IsHemiperfect 1 n ∧ ∀ {k : ℕ}, IsHemiperfect k n → Even n := by
  refine ⟨?_, fun {k} ⟨hk, _, heq⟩ ↦ ?_⟩
  · rintro ⟨_, hn, heq⟩
    have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne'⟩
    have hge : n ≤ σ 1 n := by
      rw [ArithmeticFunction.sigma_apply]
      have h1 := Finset.single_le_sum (f := fun x ↦ x ^ 1) (fun x _ ↦ Nat.zero_le _) hmem
      simpa using h1
    omega
  · obtain ⟨m, rfl⟩ := hk
    have hdvd : 2 ∣ (2 * m + 1) * n := ⟨σ 1 n, heq.symm⟩
    exact even_iff_two_dvd.mpr ((Nat.Coprime.dvd_of_dvd_mul_left (by simp) hdvd))

/-- Does any $19$-hemiperfect integer exist? -/
@[category research open, question, AMS 11]
theorem exists_nineteen_hemiperfect :
    ∃ n : ℕ, IsHemiperfect 19 n := by
  sorry

/-- Does every odd $k \ge 3$ admit a $k$-hemiperfect integer (note $k \ge 3$ is required because
no $1$-hemiperfect integer exists)? -/
@[category research open, question, AMS 11]
theorem exists_hemiperfect_forall_odd :
    ∀ k : ℕ, Odd k → 3 ≤ k → ∃ n : ℕ, IsHemiperfect k n := by
  sorry

end HemiperfectNumber
