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
public import FormalConjectures.ErdosProblems.«246»

/-!
# Erdős Problem 1110

*References:*
- [erdosproblems.com/1110](https://www.erdosproblems.com/1110)
- [Ap26] Apiros3, *Erdős Problem 1110* (2026). Lean formalisation,
  [github.com/Apiros3/erdos1110](https://github.com/Apiros3/erdos1110/tree/6d66854a3d940490c25a802b9aed54fe896ec8ec).
- [YuCh22] Yu, Wang-Xing and Chen, Yong-Gao, *On a conjecture of Erdős and Lewin*. J. Number
  Theory 238 (2022), 763--778.
-/

@[expose] public section

namespace Erdos1110

/--
$n$ is representable with respect to $p$ and $q$ if it is the sum of a finite
divisibility antichain of terms of the form $p^kq^l$.
-/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ Erdos246.Gamma p q ∧
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧
    s.sum id = n

/--
Let $p>q\geq 2$ be two coprime integers. We call $n$ representable if it is the sum of
integers of the form $p^kq^l$, none of which divide each other.

If $\{p,q\}\neq \{2,3\}$ then what can be said about the density of non-representable
numbers? Are there infinitely many coprime non-representable numbers, that is, an infinite
family of pairwise coprime non-representable integers?

We state the second question. The answer is yes. Yu and Chen [YuCh22] proved it for all pairs
except $(p, q) = (5, 2)$, $(9, 2)$ and $(5, 3)$. For these three pairs, take $c = 3$, $5$ and $2$
respectively. Then $p^a + c q^M$ is non-representable for all $a, M \geq 1$ with $p^a < q^M$ and
$c q^M < (p - 1) p^a$, and infinitely many of these numbers are pairwise coprime [Ap26].
[Ap26] is a Lean formalisation from 2026 without a published paper.
-/
@[category research solved, question, AMS 5 11]
theorem erdos_1110 :
    ∀ (p q : ℕ), q < p → 2 ≤ q →
      Nat.Coprime p q → ¬(p = 3 ∧ q = 2) →
      ∃ A : Set ℕ, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
        ∀ n ∈ A, ¬Representable p q n := by
  sorry

end Erdos1110
