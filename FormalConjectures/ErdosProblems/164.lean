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
# Erdős Problem 164

*References:*
- [erdosproblems.com/164](https://www.erdosproblems.com/164)
- [ABLLPSTT26] B. Alexeev, K. Barreto, Y. Li, J. D. Lichtman, L. Price, J. I. Shah, Q. Tang, and
  T. Tao, *Primitive sets and Von Mangoldt Chains: Erdős problem #1196 and beyond*.
  arXiv:2605.00301 (2026).
- [Er35] Erdős, Paul, *Note on Sequences of Integers No One of Which is Divisible By Any Other*.
  J. London Math. Soc. (1935), 126-128.
- [Li23] Lichtman, J. D., *A proof of the Erdős primitive set conjecture*. arXiv:2202.02384 (2023).
-/

namespace Erdos164

/-- A set `A ⊆ ℕ` is *primitive* if no member of `A` divides another. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/--
A set $A\subset \mathbb{N}$ is primitive if no member of $A$ divides another. Is the sum
\[\sum_{n\in A}\frac{1}{n\log n}\]
maximised over all primitive sets when $A$ is the set of primes?

Erdős [Er35] proved that this sum always converges for a primitive set. Lichtman [Li23] proved
that the answer is yes. An alternative, simpler, proof is given by Alexeev, Barreto, Li, Lichtman,
Price, Shah, Tang, and Tao [ABLLPSTT26].

Following the convention of [Li23] we require the members of a primitive set to be greater than
one; this excludes $A = \{1\}$, for which the summand $\frac{1}{1\cdot\log 1}$ is not defined.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos164.lean"]
theorem erdos_164 : answer(True) ↔
    IsPrimitive {p : ℕ | p.Prime} ∧
      ∀ A : Set ℕ, (∀ a ∈ A, 2 ≤ a) → IsPrimitive A →
        (∑' a : A, 1 / ((a : ℕ) * Real.log (a : ℕ))) ≤
          ∑' p : {p : ℕ | p.Prime}, 1 / ((p : ℕ) * Real.log (p : ℕ)) := by
  sorry

end Erdos164
