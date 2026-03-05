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
# Erdős Problem 419

*Reference:* [erdosproblems.com/419](https://www.erdosproblems.com/419)

If $\tau(n)$ counts the number of divisors of $n$, then what is the set of limit
points of $\tau((n+1)!) / \tau(n!)$?

Erdős and Graham [ErGr80] noted that any number of the shape $1 + 1/k$ for $k \geq 1$
is a limit point (and thus so too is $1$), but knew of no others.

Sawhney (and independently Erdős–Graham–Ivić–Pomerance [EGIP96]) proved that
these are the only limit points: the set of limit points of the ratio is
exactly $\{1 + 1/k : k \geq 1\} \cup \{1\}$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique (1980).

[EGIP96] Erdős, P., Graham, R., Ivić, A., and Pomerance, C., _On the number of
divisors of n!_. Analytic Number Theory (Proceedings of a Conference in Honor of
Heini Halberstam) (1996).
-/

open Filter

open scoped Topology

namespace Erdos419

/-- The ratio $\tau((n+1)!) / \tau(n!)$ as a real number, where $\tau$ counts divisors. -/
noncomputable def erdos419_ratio (n : ℕ) : ℝ :=
  ((Nat.divisors (n + 1).factorial).card : ℝ) / ((Nat.divisors n.factorial).card : ℝ)

/--
Erdős Problem 419 [ErGr80, p.83] [EGIP96]:

The set of limit points of $\tau((n+1)!) / \tau(n!)$ is exactly
$\{1 + 1/k : k \geq 1\} \cup \{1\}$, where $\tau(n) = |\text{divisors of } n|$.

A value $c$ is a cluster point of this sequence if and only if
$c = 1$ or $c = 1 + 1/k$ for some positive integer $k$.
-/
@[category research solved, AMS 11]
theorem erdos_419 :
    {c : ℝ | MapClusterPt c atTop erdos419_ratio} =
      answer({1} ∪ {c | ∃ k : ℕ, 0 < k ∧ c = 1 + 1 / (k : ℝ)}) := by
  sorry

end Erdos419
