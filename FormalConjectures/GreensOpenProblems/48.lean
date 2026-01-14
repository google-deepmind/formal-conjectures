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
# Ben Green's Open Problem 48

*Reference:* Ben Green, *Open Problems*, Problem 48.
See: https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.48

This entry records Green's informal question about the inverse **small sieve**:
"Suppose that a small sieve process leaves a set of maximal size. What is the
structure of that set?"

Green notes that the question is currently not well-formulated and suggests
several possible precise forms (for example, a linear sieve removing one residue
class $a(p) \pmod p$ for each prime $p \le \sqrt{X}$), and also mentions the
role of possible Siegel zeros in extremal examples.
-/

namespace Green48

/--
Ben Green's Open Problem 48 (inverse small sieve — informal).

Green's original statement is intentionally informal.  Here we record the
informal question and list a few precise variants that others may wish to
formalize or attempt:

1. (Linear sieve variant)  For each prime $p \le \sqrt{X}$ choose one residue
   class $a(p) \pmod p$ and remove it from $[X]$, leaving a set $S$. If
   $S$ attains the maximal size allowed by the Selberg/Rosser--Iwaniec bound,
   what is the structure of $S$?  Are extremal examples essentially those
   arising from Siegel zeros?

2. (Fractional sieve)  For a sieve of dimension $\kappa < 1$ (keeping a
   fraction $\kappa$ of primes), characterize the extremal sets when the
   Selberg-type bound is attained.

Because Green states that a "good formulation" is not obvious, we record the
problem as open in its current informal form.
-/
@[category research open, AMS 11]
theorem green_48 : answer(sorry) ↔
  true := by
  -- This is an open/informal problem; no formal statement is proved here.
  trivial

end Green48
