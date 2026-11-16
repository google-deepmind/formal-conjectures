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
# Erdős Problem 676

*References:*
- [erdosproblems.com/676](https://www.erdosproblems.com/676)
- [Er79] Erdős, Paul, *Some unconventional problems in number theory*.
  Math. Mag. (1979), 67–70.
- [Er79d] Erdős, P., *Some unconventional problems in number theory*.
  Acta Math. Acad. Sci. Hungar. (1979), 71–80.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*.
  Ann. Discrete Math. (1980), 89–115.
-/

@[expose] public section

namespace Erdos676

open Filter

/-- An integer has a representation $ap^2+b$ with $p$ prime, $a \geq 1$, and $b < p$
if and only if $p^2 \leq n$ and $n \bmod p^2 < p$ for some prime $p$. -/
@[category test, AMS 11]
theorem representation_iff_mod (n : ℕ) :
    (∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b) ↔
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ≤ n ∧ n % p ^ 2 < p := by
  constructor
  · rintro ⟨a, p, b, hp, ha, hb, rfl⟩
    refine ⟨p, hp, ?_, ?_⟩
    · nlinarith
    · have hb' : b < p ^ 2 := by
        have := hp.two_le
        nlinarith
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb'] using hb
  · rintro ⟨p, hp, hn, hr⟩
    refine ⟨n / p ^ 2, p, n % p ^ 2, hp, ?_, hr, ?_⟩
    · exact Nat.div_pos hn (pow_pos hp.pos _)
    · simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n (p ^ 2)).symm

/-- The integer $35$ has no representation $ap^2+b$ of the required form. -/
@[category test, AMS 11]
theorem not_representable_35 :
    ¬ ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ 35 = a * p ^ 2 + b := by
  rw [representation_iff_mod]
  rintro ⟨p, hp, hn, hr⟩
  have hp6 : p < 6 := by nlinarith
  have hc : ∀ q : Fin 6, ¬ (q.val.Prime ∧ q.val ^ 2 ≤ 35 ∧ 35 % q.val ^ 2 < q.val) :=
    by decide
  exact hc ⟨p, hp6⟩ ⟨hp, hn, hr⟩

/-- The integer $899$ has no representation $ap^2+b$ of the required form. -/
@[category test, AMS 11]
theorem not_representable_899 :
    ¬ ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ 899 = a * p ^ 2 + b := by
  rw [representation_iff_mod]
  rintro ⟨p, hp, hn, hr⟩
  have hp30 : p < 30 := by nlinarith
  have hc : ∀ q : Fin 30, ¬ (q.val.Prime ∧ q.val ^ 2 ≤ 899 ∧ 899 % q.val ^ 2 < q.val) :=
    by decide
  exact hc ⟨p, hp30⟩ ⟨hp, hn, hr⟩

/-- Is every sufficiently large integer of the form $ap^2+b$ for some prime $p$ and integers
$a \geq 1$ and $0 \leq b < p$? -/
@[category research open, question, AMS 11]
theorem erdos_676 : ∀ᶠ n in atTop,
    ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b := by
  sorry

/- TODO: Formalize the source's additional variants: the quantitative almost-all result, the
version without primality, the general pair $(A,f)$, and the questions about the minimal $c_n$. -/

end Erdos676
