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
# Erdős Problem 722

*Reference:* [erdosproblems.com/722](https://www.erdosproblems.com/722)

Let $k > r$ and $n$ be sufficiently large in terms of $k$ and $r$. Does there always
exist a Steiner system $S(r, k, n)$, provided the trivial necessary divisibility
conditions $\binom{k-i}{r-i} \mid \binom{n-i}{r-i}$ are satisfied for every $0 \le i < r$?

That is, can one find a family of $\binom{n}{k}/\binom{k}{r}$ many $k$-element subsets of
$\{1, \ldots, n\}$ such that every $r$-element subset is contained in exactly one set
in the family?

This was proved for $(r,k)$ by:
- Kirkman for $(2,3)$;
- Hanani [Ha61] for $(3,4)$, $(2,4)$, and $(2,5)$;
- Wilson [Wi72] for $(2,k)$ for any $k$;
- Keevash [Ke14] for all $(r,k)$.

[Ha61] Hanani, H., *The existence and construction of balanced incomplete block designs*,
Ann. Math. Statist. 32 (1961), 361-386.

[Wi72] Wilson, R. M., *An existence theory for pairwise balanced designs I-III*,
J. Combin. Theory Ser. A (1972-1975).

[Ke14] Keevash, P., *The existence of designs*, arXiv:1401.3665 (2014).
-/

open Finset Nat

namespace Erdos722

/-- A Steiner system $S(r, k, n)$: a collection $F$ of $k$-element subsets of `Fin n`
such that every $r$-element subset of `Fin n` is contained in exactly one
member of $F$. -/
def IsSteinerSystem (r k n : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ F, B.card = k) ∧
  (∀ A : Finset (Fin n), A.card = r →
    ∃! B, B ∈ F ∧ A ⊆ B)

/-- The necessary divisibility conditions for a Steiner system $S(r, k, n)$:
for every $0 \le i < r$, $\binom{k-i}{r-i} \mid \binom{n-i}{r-i}$. -/
def SteinerDivisibilityConditions (r k n : ℕ) : Prop :=
  ∀ i < r, (Nat.choose (k - i) (r - i)) ∣ (Nat.choose (n - i) (r - i))

/--
Erdős Problem 722 (Keevash's theorem [Ke14]):

For every $k > r \ge 1$, there exists $N_0$ such that for all $n \ge N_0$, if the
necessary divisibility conditions are satisfied, then a Steiner system
$S(r, k, n)$ exists.
-/
@[category research solved, AMS 5]
theorem erdos_722 : answer(True) ↔
    ∀ (r k : ℕ), r ≥ 1 → k > r →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        SteinerDivisibilityConditions r k n →
        ∃ F : Finset (Finset (Fin n)), IsSteinerSystem r k n F := by
  sorry

end Erdos722
