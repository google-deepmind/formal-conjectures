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

*References:*
- [erdosproblems.com/429](https://www.erdosproblems.com/429)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*.
  Ann. Discrete Math. (1980), 89-115.
- [We24] D. Weisenberg, *Sparse Admissible Sets and a Problem of Erdős and Graham*.
  Integers (2024).
-/

open Filter

namespace Erdos429

/--
Is it true that, if $A\subseteq \mathbb{N}$ is sparse enough and does not cover all residue
classes modulo $p$ for any prime $p$, then there exists some $n$ such that $n+a$ is prime for
all $a\in A$?

Weisenberg [We24] has shown the answer is no: $A$ can be arbitrarily sparse and missing at
least one residue class modulo every prime $p$, and yet $A+n$ is not contained in the primes
for any $n\in \mathbb{Z}$. (Weisenberg gives several constructions of such an $A$.)

The statement below formalizes "sparse enough" via a threshold: is there some
$f:\mathbb{N}\to\mathbb{N}$ with $f(N)\to\infty$ such that every infinite $A$ with
$\lvert A\cap[1,N]\rvert\leq f(N)$ for all $N$, missing a residue class modulo every prime,
admits such an $n$? Weisenberg's constructions refute this for every choice of $f$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos429.lean"]
theorem erdos_429 : answer(False) ↔
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ A : Set ℕ, A.Infinite → (∀ N, (A ∩ Set.Icc 1 N).ncard ≤ f N) →
        (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ b) →
        ∃ n : ℕ, ∀ a ∈ A, (n + a).Prime := by
  sorry

end Erdos429
