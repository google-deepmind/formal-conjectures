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

import FormalConjecturesUtil

/-!
# Erdős Problem 481

*References:*
- [erdosproblems.com/481](https://www.erdosproblems.com/481)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980), p.96.
- [Kl82] Klarner, David A., *A sufficient condition for certain semigroups to be free*.
  J. Algebra (1982), 140-148.
- [KoTa22] Kolpakov, Alexander and Talambutsa, Alexey, *On free semigroups of affine maps on the
  real line*. Proc. Amer. Math. Soc. (2022), 2301-2307.
-/

namespace Erdos481

/--
For a finite sequence of $n$ (not necessarily distinct) integers $A = (x_1,\ldots,x_n)$, the
sequence `T a b A` of length $rn$ given by $(a_ix_j+b_i)_{1\leq j\leq n, 1\leq i\leq r}$.
-/
def T {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap (fun i : Fin r => A.map (fun x : ℕ => a i * x + b i))

/--
Let $a_1,\ldots,a_r,b_1,\ldots,b_r\in \mathbb{N}$ such that $\sum_{i}\frac{1}{a_i}>1$. For any
finite sequence of $n$ (not necessarily distinct) integers $A=(x_1,\ldots,x_n)$ let $T(A)$ denote
the sequence of length $rn$ given by
\[(a_ix_j+b_i)_{1\leq j\leq n, 1\leq i\leq r}.\]
Prove that, if $A_1=(1)$ and $A_{i+1}=T(A_i)$, then there must be some $A_k$ with repeated
elements.

This is true. This appears to have first been shown by Klarner [Kl82], with a generalisation
given by Kolpakov and Talambutsa [KoTa22]. Essentially the same proof was found independently by
Barreto in the comment section.
-/
@[category research solved, AMS 5 11]
theorem erdos_481 {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i)
    (hab : 1 < ∑ i, (1 : ℝ) / a i) :
    ∃ k, ¬ ((T a b)^[k] [1]).Nodup := by
  sorry

end Erdos481
