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
# Erdős Problem 544

*Reference:* [erdosproblems.com/544](https://www.erdosproblems.com/544)

Show that $R(3,k+1) - R(3,k) \to \infty$ as $k \to \infty$.
Similarly, prove or disprove that $R(3,k+1) - R(3,k) = o(k)$.

A problem of Erdős and Sós. See also [165] and [1014].

[Er81c] Erdős, P., _Some problems in combinatorics, graph theory and probability_ (1981).

[Er93] Erdős, P., _Some of my favourite problems in various branches of combinatorics_ (1993), p. 339.
-/

open SimpleGraph Filter

namespace Erdos544

/-- The Ramsey number $R(3,k)$: the minimum $N$ such that every simple graph
on $N$ vertices contains either a triangle ($3$-clique) or an independent
set of size $k$ (a $k$-clique in the complement). -/
noncomputable def ramseyR3 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Problem 544 (Part 1) [Er81c][Er93, p. 339]:

Show that $R(3,k+1) - R(3,k) \to \infty$ as $k \to \infty$.

That is, the consecutive differences of the Ramsey numbers $R(3,k)$
tend to infinity.
-/
@[category research open, AMS 5]
theorem erdos_544 :
    Tendsto (fun k : ℕ => (ramseyR3 (k + 1) : ℤ) - (ramseyR3 k : ℤ))
      atTop atTop := by
  sorry

/--
Erdős Problem 544 (Part 2) [Er81c][Er93, p. 339]:

Prove or disprove that $R(3,k+1) - R(3,k) = o(k)$, i.e.,
$(R(3,k+1) - R(3,k)) / k \to 0$ as $k \to \infty$.
-/
@[category research open, AMS 5]
theorem erdos_544.variants.little_o : answer(sorry) ↔
    Tendsto (fun k : ℕ => ((ramseyR3 (k + 1) : ℝ) - (ramseyR3 k : ℝ)) / (k : ℝ))
      atTop (nhds 0) := by
  sorry

end Erdos544
