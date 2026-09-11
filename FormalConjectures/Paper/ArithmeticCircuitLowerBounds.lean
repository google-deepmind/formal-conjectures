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
# The permanent arithmetic-circuit lower-bound conjecture

*References:*
* Shpilka and Yehudayoff, *Arithmetic circuits: A survey of recent results and open
questions*, Foundations and Trends in Theoretical Computer Science 5(3–4), 207–388,
https://www.cs.tau.ac.il/~shpilka/publications/SY10.pdf,
Definition 1.1, Definition 1.2, Valiant's hypothesis I, and Theorem 1.1
(author-version pp. 2–5).

-/

namespace ShpilkaYehudayoff

/-- **Permanent circuit lower bound** (Shpilka–Yehudayoff, Definitions 1.1–1.2,
Valiant's hypothesis I and Theorem 1.1, pp. 2–5). There are no constants $C,d$ such
that for every $n$, the generic $n\times n$ permanent over $\mathbb{Q}$ is computed
by a division-free $+,\times$ circuit with at most $C(n+1)^d$ edges. Arbitrary rational
constants and shared fan-out are allowed; their bit lengths and intermediate degrees
are unbounded. The family is nonuniform, and $n=0$ has permanent one. By permanent
completeness this is $VP_{\mathbb{Q}}\ne VNP_{\mathbb{Q}}$, an algebraic analogue of
$P\ne NP$, not an asserted equivalent of the Boolean conjecture. -/
@[category research open, AMS 13 68]
theorem permanent_not_polynomial_size :
    ¬ AlgebraicProblems.HasPolynomialSizePermanentCircuits := by
  sorry

end ShpilkaYehudayoff
