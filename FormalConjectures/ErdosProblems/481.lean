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

Let $a_1, \ldots, a_r, b_1, \ldots, b_r \in \mathbb{N}$ with $\sum 1/a_i > 1$. Starting from
$A_1 = (1)$ and iterating $T(A) = (a_i x_j + b_i)$, prove that some $A_k$ must contain repeated
elements.

*Reference:* [erdosproblems.com/481](https://www.erdosproblems.com/481)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Kl82] Klarner, D., _A sufficient condition for certain semigroups to be free_. J. Algebra
(1982), 140–148.

[KoTa22] Kolpakov, A. and Talambutsa, A., _On free semigroups of affine maps on the real line_.
Proc. Amer. Math. Soc. (2022), 2301–2307.
-/

namespace Erdos481

/-- The affine map transformation $T$ from Erdős Problem 481.
Given parameters $(a_i, b_i)$ and a sequence $A = (x_1, \ldots, x_n)$,
$T(A)$ is the sequence $(a_i x_j + b_i)_{1 \le j \le n, 1 \le i \le r}$. -/
def affineTransform (params : List (ℕ × ℕ)) (A : List ℤ) : List ℤ :=
  A.flatMap (fun x => params.map (fun ⟨a, b⟩ => (a : ℤ) * x + (b : ℤ)))

/-- Iterate the affine transform starting from $A_1 = (1)$.
`iterateAffine params 0 = [1]` and `iterateAffine params (k+1) = T(iterateAffine params k)`. -/
def iterateAffine (params : List (ℕ × ℕ)) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => affineTransform params (iterateAffine params n)

/--
Erdős Problem 481 [ErGr80, p.96]:

Let $a_1, \ldots, a_r, b_1, \ldots, b_r \in \mathbb{N}$ with $\sum_i 1/a_i > 1$.
For a finite sequence $A = (x_1, \ldots, x_n)$ of (not necessarily distinct) integers,
let $T(A)$ denote the sequence of length $rn$ given by
$(a_i x_j + b_i)_{1 \le j \le n, 1 \le i \le r}$.
If $A_1 = (1)$ and $A_{k+1} = T(A_k)$, then there must be some $A_k$ with
repeated elements.
-/
@[category research solved, AMS 5 11]
theorem erdos_481
    (params : List (ℕ × ℕ))
    (hne : params ≠ [])
    (hpos : ∀ p ∈ params, 0 < p.1)
    (hsum : (params.map (fun p => (1 : ℝ) / (p.1 : ℝ))).sum > 1) :
    ∃ k : ℕ, ¬ (iterateAffine params k).Nodup := by
  sorry

end Erdos481
