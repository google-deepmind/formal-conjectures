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
# Erdős Problem 328

*Reference:* [erdosproblems.com/328](https://www.erdosproblems.com/328)

Suppose $A \subseteq \mathbb{N}$ has bounded additive representation function
($1_A * 1_A(n) \leq C$ for all $n$). Can $A$ be partitioned into finitely many subsets,
each with strictly smaller representation function? Nešetřil and Rödl showed the answer is no.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[NeRo85] Nešetřil, J. and Rödl, V. (1985).
-/

open Classical Finset

namespace Erdos328

/-- The additive representation count: the number of pairs $(a, b)$ with $a + b = n$
and both $a, b \in A$. This formalizes $1_A * 1_A(n)$. -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
Erdős Problem 328 [ErGr80, p.48]:

Suppose $A \subseteq \mathbb{N}$ and $C > 0$ is such that $1_A * 1_A(n) \leq C$ for all
$n \in \mathbb{N}$. Can $A$ be partitioned into $t$ many subsets $A_1, \ldots, A_t$
(where $t = t(C)$ depends only on $C$) such that $1_{A_i} * 1_{A_i}(n) < C$ for all
$1 \leq i \leq t$ and $n \in \mathbb{N}$?

Asked by Erdős and Newman. Nešetřil and Rödl [NeRo85] showed the answer is no
for all $C$ (even if $t$ is also allowed to depend on $A$).
-/
@[category research solved, AMS 5 11]
theorem erdos_328 : answer(False) ↔
    ∀ C : ℕ, 1 ≤ C →
      ∀ A : Set ℕ, (∀ n, repCount A n ≤ C) →
        ∃ t : ℕ, 1 ≤ t ∧
          ∃ f : ℕ → Fin t,
            ∀ (i : Fin t) (n : ℕ),
              repCount ({a | a ∈ A ∧ f a = i}) n < C := by
  sorry

end Erdos328
