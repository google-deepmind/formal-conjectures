/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1043

*Reference:* [erdosproblems.com/1043](https://www.erdosproblems.com/1043)
-/

namespace Erdos1043

open Complex MeasureTheory Set

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ -/
def LevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖Polynomial.eval z f‖ ≤ 1}

/--
**Erdős Problem 1043**: Let $f\in \mathbb{C}[x]$ be a monic polynomial.
Must there exist a straight line $\ell$ such that the projection of
\[\{ z: \lvert f(z)\rvert\leq 1\}\]
onto $\ell$ has measure at most $2$?

Note: A straight line $\ell$ can be parameterized as $\{t u \mid t \in \mathbb{R}\}$ for some
unit vector $u \in \mathbb{C}$ (up to translation, which does not affect the measure of the projection).
The projection onto this line, when mapped to $\mathbb{R}$, is given by $z \mapsto \operatorname{re}(\overline{u} z)$.
We use `star u` for $\overline{u}$ which is the generic notation for conjugation on a star-ring.
The measure on the line is the 1-dimensional Lebesgue measure, which is `volume` on $\mathbb{R}$.
The problem is known to be solved (it is true, conjectured by Erdős and proved by Pommerenke in 1976).
-/
@[category research solved, AMS 28 30]
theorem erdos_1043 :
  ∀ (f : Polynomial ℂ), f.Monic →
    ∃ (u : ℂ), ‖u‖ = 1 ∧
    volume ((fun z : ℂ => (star u * z).re) '' (LevelSet f)) ≤ 2 :=
by sorry

end Erdos1043
