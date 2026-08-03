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
# Erdős Problem 481

*References:*
- [erdosproblems.com/481](https://www.erdosproblems.com/481)
- [ErGr80] Erdős, P. and Graham, R. L., Old and new problems and results in combinatorial
  number theory. (1980), p. 96.
- [Kl82] Klarner, D. A., A sufficient condition for certain semigroups to be free. J. Algebra
  (1982), 140-148.
-/

namespace Erdos481

/-- The constant $C = \sum_i 1/a_i$. -/
noncomputable def C {r : ℕ} (a : Fin r → ℕ+) : ℝ :=
  ∑ i : Fin r, (1 : ℝ) / (a i : ℝ)

/-- The transformation `T` applied to a list of positive integers. -/
def T {r : ℕ} (a b : Fin r → ℕ+) (L : List ℕ+) : List ℕ+ :=
  L.flatMap fun x : ℕ+ => (List.finRange r).map fun i =>
    ⟨a i * x + b i, Nat.add_pos_right _ (b i).2⟩

/-- The sequence `A_k`, with `A_1 = [1]` and `A_{k+1} = T(A_k)`. -/
def A {r : ℕ} (a b : Fin r → ℕ+) : ℕ → List ℕ+
  | 0 => []
  | 1 => [1]
  | n + 2 => T a b (A a b (n + 1))

/--
Let $a_1,\ldots,a_r,b_1,\ldots,b_r\in \mathbb{N}$ such that
$\sum_i 1/a_i > 1$. For any finite sequence of $n$ (not necessarily distinct) integers
$A=(x_1,\ldots,x_n)$ let $T(A)$ denote the sequence of length $rn$ given by
$(a_i x_j + b_i)_{1\leq j\leq n,1\leq i\leq r}$.

If $A_1=(1)$ and $A_{i+1}=T(A_i)$, then there must be some $A_k$ with repeated elements.
-/
@[category research solved, AMS 11,
formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.30.0/ErdosProblems/Erdos481.lean#L382"]
theorem erdos_481 : answer(True) ↔
    ∀ {r : ℕ} (a b : Fin r → ℕ+), 0 < r → 1 < C a →
      ∃ k, 1 ≤ k ∧ ¬ (A a b k).Nodup := by
  sorry

end Erdos481
