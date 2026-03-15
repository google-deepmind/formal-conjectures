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
# Erdős Problem 429

Erdős asked whether every infinite admissible set of natural numbers has a translate contained
in the primes. Weisenberg showed the answer is no.

*Reference:* [erdosproblems.com/429](https://www.erdosproblems.com/429)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p. 85.

[We24] Weisenberg, D., *Sparse Admissible Sets and a Problem of Erdős and Graham*. Integers (2024).
-/

namespace Erdos429

/--
Is it true that, if $A \subseteq \mathbb{N}$ is sparse enough and does not cover all residue
classes modulo $p$ for any prime $p$, then there exists some $n$ such that $n + a$
is prime for all $a \in A$?

A set $A \subseteq \mathbb{N}$ is called "admissible" if for every prime $p$, there exists a
residue class modulo $p$ not represented in $A$. This is a necessary condition
for the translate $A + n$ to consist entirely of primes.

Weisenberg [We24] has shown the answer is no: $A$ can be arbitrarily sparse
and missing at least one residue class modulo every prime $p$, and yet $A + n$
is not contained in the primes for any $n \in \mathbb{Z}$.

We formalize the conjecture for infinite admissible sets $A \subseteq \mathbb{N}$.
-/
@[category research solved, AMS 11]
theorem erdos_429 :
    answer(False) ↔
    ∀ (A : Set ℕ),
      Set.Infinite A →
      (∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r) →
      ∃ n : ℕ, ∀ a ∈ A, (n + a).Prime := by
  sorry

end Erdos429
