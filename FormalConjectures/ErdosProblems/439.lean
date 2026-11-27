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

/-!
# Erdős Problem 439

*References:*
- [erdosproblems.com/439](https://www.erdosproblems.com/439)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Er80c] Erdős, Paul, *Nine little known problems in combinatorial number theory*. Normat (1980),
  155-164, 180.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErSa77] Erdős, P. and Sárközy, A., *On differences and sums of integers. II*. Bull. Soc. Math.
  Grèce (N.S.) (1977), 204-223.
- [ESS89] Erdős, P. and Sárközy, A. and Sós, V. T., *On a conjecture of Roth and some related
  problems. I*. (1989), 47-59.
- [KhSz06] Khalfalah, Ayman and Szemerédi, Endre, *On the number of monochromatic solutions of
  $x+y=z^2$*. Combin. Probab. Comput. (2006), 213-227.
-/

@[expose] public section

namespace Erdos439

/--
Is it true that, in any finite colouring of the integers, there must be two integers $x\neq y$ of
the same colour such that $x+y$ is a square?

Equivalently, the graph on the positive integers joining $m$ and $n$ when $m+n$ is a square has
infinite chromatic number. Erdős, Sárközy, and Sós [ESS89] proved this for $2$ or $3$ colours.
The answer is yes, as proved by Khalfalah and Szemerédi [KhSz06].

We colour the positive integers, as in [ESS89].
-/
@[category research solved, question, AMS 5 11]
theorem erdos_439 :
    ∀ (r : ℕ) (c : ℕ → Fin r), ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧
      IsSquare (x + y) := by
  sorry

/--
What about a $k$th power? In any finite colouring of the positive integers, there are $x\neq y$
of the same colour such that $x+y$ is a $k$th power.

This also follows from Khalfalah and Szemerédi [KhSz06], who prove the result with $x+y=z^2$
replaced by $x+y=f(z)$ for suitable non-constant $f\in\mathbb{Z}[z]$, including $f(z)=z^k$.
-/
@[category research solved, question, AMS 5 11]
theorem erdos_439.variants.pow (k : ℕ) (hk : 1 ≤ k) :
    ∀ (r : ℕ) (c : ℕ → Fin r), ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧
      ∃ z : ℕ, x + y = z ^ k := by
  sorry

end Erdos439
