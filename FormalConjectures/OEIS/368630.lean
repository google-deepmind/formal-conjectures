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
# A self-compositional exponential generating function

The normalized exponential generating function of OEIS A368630 satisfies
$A(x/A(x)^2)=\exp(xA(x))$, with $A(0)=1$.

*References:*
- [A368630](https://oeis.org/A368630), Paul D. Hanna, 2024.
- [Li26] Wentao Li, [Congruences of the exponential generating sequence](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/e0e499973c3398f08ed91b39618f1948fe1804a5/proofs/new-proofs/A368630/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA368630
open PowerSeries

/-- The rational exponential generating series of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- The defining equation for the integer EGF coefficients of OEIS A368630. -/
def IsGeneratingSequence (c : ℕ → ℤ) : Prop :=
  (egf c).constantCoeff = 1 ∧
    (egf c).subst (X * ((egf c)⁻¹) ^ 2) = (exp ℚ).subst (X * egf c)

/-- The integer coefficients of the normalized exponential generating function. -/
noncomputable def a : ℕ → ℤ := Classical.epsilon IsGeneratingSequence

/-- The original equation defines a unique integer coefficient sequence; see [Li26]. -/
@[category API, AMS 11 13,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/e0e499973c3398f08ed91b39618f1948fe1804a5/LeanOeisProofs/NewProofs/A368630.lean#L1003"]
theorem exists_unique_sequence : ∃! c : ℕ → ℤ, IsGeneratingSequence c := by
  sorry

/-- The selected sequence satisfies the defining equation. -/
@[category API, AMS 11 13]
theorem a_spec : IsGeneratingSequence a :=
  Classical.epsilon_spec exists_unique_sequence.exists

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h := a_spec.1
  norm_num [egf] at h
  exact_mod_cast h

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 7 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 136 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 4933 := by
  sorry

/--
For every $n \ge 0$, "a(n) == 1 (mod 3)".
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/e0e499973c3398f08ed91b39618f1948fe1804a5/LeanOeisProofs/NewProofs/A368630.lean#L1017"]
theorem conjecture_mod_three (n : ℕ) : a n % 3 = 1 := by
  sorry

/--
For every $n \ge 0$, "a(2*n) == 1 (mod 2)".
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/e0e499973c3398f08ed91b39618f1948fe1804a5/LeanOeisProofs/NewProofs/A368630.lean#L1023"]
theorem conjecture_even (n : ℕ) : a (2 * n) % 2 = 1 := by
  sorry

/--
For every $n \ge 1$, "a(2*n+1) == 0 (mod 2)". The term $a(1)=1$ is excluded.
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/e0e499973c3398f08ed91b39618f1948fe1804a5/LeanOeisProofs/NewProofs/A368630.lean#L1028"]
theorem conjecture_odd (n : ℕ) (hn : 1 ≤ n) : a (2 * n + 1) % 2 = 0 := by
  sorry

end OeisA368630
