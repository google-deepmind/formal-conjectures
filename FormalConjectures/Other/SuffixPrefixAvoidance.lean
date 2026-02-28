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
# Suffix-prefix avoidance bound

Let $A$ and $B$ be sets of words of length $n$ over an alphabet with $q$ letters. If no
(nonempty) suffix of any word in $A$ coincides with a prefix of any word in $B$, then
$$|A| \cdot |B| \leq \frac{q^{2n}}{en}.$$

*Reference:*
- [X post by Dmitry Rybin](https://x.com/DmitryRybin1/status/2027278135847428577)
-/

open Finset Real

namespace SuffixPrefixAvoidance

variable {n q : ℕ}

/-- The suffix of a word `w : Fin n → Fin q` of length `k + 1` (the last `k + 1` characters). -/
def wordSuffix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of a word `w : Fin n → Fin q` of length `k + 1` (the first `k + 1` characters). -/
def wordPrefix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨i, by omega⟩

/-- Two sets of words $A, B$ over `Fin q` of length `n` are suffix-prefix avoiding if no
nonempty suffix of any word in $A$ equals any prefix of any word in $B$ of the same length. -/
def IsSuffixPrefixAvoiding (A B : Finset (Fin n → Fin q)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ k : Fin n, wordSuffix a k ≠ wordPrefix b k

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q$ letters.
Trivially then $|A| \cdot |B|$ is at most $q^{2n}$.
-/
@[category test, AMS 5]
theorem words_naive_bound
    (A B : Finset (Fin n → Fin q)) :
    A.card * B.card ≤ q ^ (2 * n) := by
  simp [Nat.mul_le_mul, two_mul, pow_add, (Finset.card_le_univ _).trans_eq]

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
No suffix of a word in $A$ coincides with a prefix of a word in $B$.
Prove that then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{en}$.
-/
-- TODO(firsching): update problem status when solution becomes public
@[category research open, AMS 5]
theorem suffix_prefix_avoidance_bound
    (A B : Finset (Fin n → Fin q))
    (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  sorry

/--
$A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
No suffix of a word in $A$ coincides with a prefix of a word in $B$.
Then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{n}$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/102e47fee802d461946e3a4e0b47fdbe7db4c1ed/FormalConjectures/Other/SuffixPrefixAvoidance.lean#L157", AMS 5]
theorem suffix_prefix_avoidance_weaker_bound
    (A B : Finset (Fin n → Fin q))
    (_hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℚ) * B.card ≤ (q : ℚ) ^ (2 * n) / n := by
  sorry

end SuffixPrefixAvoidance
