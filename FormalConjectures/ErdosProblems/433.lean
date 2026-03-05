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
# Erdős Problem 433

*Reference:* [erdosproblems.com/433](https://www.erdosproblems.com/433)

If $A \subset \mathbb{N}$ is a finite set with $\gcd(A) = 1$, let $G(A)$ denote the Frobenius
number: the greatest natural number not expressible as a non-negative integer linear combination of
elements of $A$ (with repetitions allowed). Define
$$g(k,n) = \max G(A)$$
where the maximum is over all $A \subseteq \{1,\ldots,n\}$ with $|A| = k$ and $\gcd(A) = 1$.

Is it true that $g(k,n) \sim n^2/(k-1)$?

This was proved by Dixmier [Di90], who showed that for all $2 \leq k < n$,
$$\lfloor(n-2)/(k-1)\rfloor(n-k+1) - 1 \leq g(k,n) \leq (\lfloor(n-1)/(k-1)\rfloor - 1)n - 1.$$

[Di90] Dixmier, J., _Proof of a conjecture by Erdős and Graham concerning the problem of
Frobenius_. J. London Math. Soc. (2) 41 (1990), 227-237.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Filter Asymptotics

namespace Erdos433

/-- A natural number $m$ is representable by a finite set $A$ if it equals
$\sum_{a \in A} f(a) \cdot a$ for some coefficient function $f : \mathbb{N} \to \mathbb{N}$. -/
def Representable433 (A : Finset ℕ) (m : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, ∑ a ∈ A, f a * a = m

/-- The Frobenius number of $A$: the supremum of natural numbers not representable
as a non-negative integer linear combination of elements of $A$. Equals $0$ when
every natural number is representable (e.g., when $1 \in A$). -/
noncomputable def FrobeniusNumber433 (A : Finset ℕ) : ℕ :=
  sSup {m : ℕ | ¬ Representable433 A m}

/-- $g(k,n) = \max G(A)$ over all $A \subseteq \{1,\ldots,n\}$ with $|A| = k$ and
$\gcd(A) = 1$. -/
noncomputable def g433 (k n : ℕ) : ℕ :=
  sSup (FrobeniusNumber433 '' {A : Finset ℕ | A ⊆ Icc 1 n ∧ A.card = k ∧ A.gcd id = 1})

/--
Erdős Problem 433 [ErGr80]:

For any fixed $k \geq 2$, $g(k,n) \sim n^2/(k-1)$ as $n \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_433 : answer(True) ↔
    ∀ k : ℕ, 2 ≤ k →
      (fun n : ℕ => (g433 k n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 / ((k : ℝ) - 1)) := by
  sorry

end Erdos433
