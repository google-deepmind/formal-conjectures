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
# Ramsey Number R(5,5)

The Ramsey number $R(s, t)$ is the smallest positive integer $n$ such that every 2-coloring of
the edges of the complete graph $K_n$ contains either a monochromatic clique of size $s$ or a
monochromatic independent set of size $t$.

The exact value of $R(5,5)$ is unknown. The best known bounds are $43 \le R(5,5) \le 48$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Ramsey%27s_theorem#Ramsey_numbers)
- [Ramsey Number — Wolfram MathWorld](https://mathworld.wolfram.com/RamseyNumber.html)
- [OEIS A212954](https://oeis.org/A212954)
-/

namespace RamseyNumberR55

open SimpleGraph

/--
The classical Ramsey number $R(s, t)$ is the smallest $n$ such that for every simple graph $G$
on $n$ vertices, $G$ contains a clique of size $s$ or its complement contains a clique of size $t$.
-/
noncomputable def ramseyNumber (s t : ℕ) : ℕ :=
  sInf { n : ℕ | ∀ G : SimpleGraph (Fin n),
    (∃ S : Finset (Fin n), S.card = s ∧ G.IsClique ↑S) ∨
    (∃ T : Finset (Fin n), T.card = t ∧ Gᶜ.IsClique ↑T) }

/--
The best known bounds on the Ramsey number $R(5,5)$ are $43 \le R(5,5) \le 48$.
The lower bound ($43 \le R(5,5)$) follows from an explicit 2-coloring of $K_{42}$ with no
monochromatic clique of size 5; the upper bound ($R(5,5) \le 48$) is established by recursive
Ramsey bounds.

Determining the exact value of $R(5,5)$ is an open problem.
-/
@[category research open, AMS 05]
theorem ramsey_number_R55 : 43 ≤ ramseyNumber 5 5 ∧ ramseyNumber 5 5 ≤ 48 := by
  sorry

end RamseyNumberR55
