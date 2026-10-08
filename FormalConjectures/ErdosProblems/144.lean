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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 144

*Reference:* [erdosproblems.com/144](https://www.erdosproblems.com/144)

[MaTe84] Maier, H. and Tenenbaum, G., On the set of divisors of an integer.
  Invent. Math. 76 (1984), 121-128.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos144

/-- The set of integers `n` having two divisors `d₁ < d₂ < c · d₁`. -/
def closeDivisorSet (c : ℝ) : Set ℕ :=
  {n | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ (d₂ : ℝ) < c * d₁}

/-- The set of integers `n` having two divisors `d₁ < d₂ < d₁ (1 + (log n)^(-β))`. -/
def veryCloseDivisorSet (β : ℝ) : Set ℕ :=
  {n | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧
    (d₂ : ℝ) < d₁ * (1 + Real.log n ^ (-β))}

/--
The density of integers which have two divisors $d_1, d_2$ such that $d_1 < d_2 < 2 d_1$
exists and is equal to $1$.

Proved by Maier and Tenenbaum [MaTe84].
-/
@[category research solved, AMS 11]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos144.lean#L94"]
theorem erdos_144 :
    Set.HasDensity {n : ℕ | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁} 1 := by
  sorry

/--
Stronger version: for every $c > 1$, the set of integers having two divisors
$d_1 < d_2 < c d_1$ has density $1$.

Proved by Maier and Tenenbaum [MaTe84].
-/
@[category research solved, AMS 11]
theorem erdos_144.variants.strong (c : ℝ) (hc : 1 < c) :
    (closeDivisorSet c).HasDensity 1 := by
  sorry

/--
Maier–Tenenbaum [MaTe84]: if $\beta < \log 3 - 1$, the set of $n$ with divisors
$d_1 < d_2 < d_1 (1 + (\log n)^{-\beta})$ has density $1$.
-/
@[category research solved, AMS 11]
theorem erdos_144.variants.maier_tenenbaum (β : ℝ) (hβ : β < Real.log 3 - 1) :
    (veryCloseDivisorSet β).HasDensity 1 := by
  sorry

/--
Erdős–Hall: if $\beta > \log 3 - 1$, the set of $n$ with divisors
$d_1 < d_2 < d_1 (1 + (\log n)^{-\beta})$ has density $0$.
-/
@[category research solved, AMS 11]
theorem erdos_144.variants.erdos_hall (β : ℝ) (hβ : Real.log 3 - 1 < β) :
    (veryCloseDivisorSet β).HasDensity 0 := by
  sorry

/-- The set in the original problem is `closeDivisorSet 2`. -/
@[category API, AMS 11]
theorem closeDivisorSet_two :
    closeDivisorSet 2 = {n | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁} := by
  ext n
  simp only [closeDivisorSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    exact ⟨a, b, ha, hb, hab, by exact_mod_cast h⟩
  · rintro ⟨a, b, ha, hb, hab, h⟩
    exact ⟨a, b, ha, hb, hab, by exact_mod_cast h⟩

/-- The original problem is the case `c = 2` of the stronger version. -/
@[category test, AMS 11]
theorem erdos_144_of_strong
    (h : ∀ c : ℝ, 1 < c → (closeDivisorSet c).HasDensity 1) :
    Set.HasDensity {n : ℕ | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁} 1 := by
  rw [← closeDivisorSet_two]
  exact h 2 one_lt_two

/-- The set `closeDivisorSet c` is closed under taking multiples. -/
@[category API, AMS 11]
theorem closeDivisorSet_mul {c : ℝ} {n : ℕ} (hn : n ∈ closeDivisorSet c) (m : ℕ) :
    n * m ∈ closeDivisorSet c := by
  obtain ⟨a, b, ha, hb, hab, h⟩ := hn
  exact ⟨a, b, ha.mul_right m, hb.mul_right m, hab, h⟩

end Erdos144
