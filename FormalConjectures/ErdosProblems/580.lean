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
# Erdős Problem 580

*References:*
- [erdosproblems.com/580](https://www.erdosproblems.com/580)
- [AKS95] Ajtai, M., Komlós, J., and Szemerédi, E., *On a conjecture of Loebl*. Graph theory,
  combinatorics, and algorithms, Vol. 1, 2 (Kalamazoo, MI, 1992) (1995), 1135-1146.
- [EFLS95] Erdős, P., Füredi, Z., Loebl, M., and Sós, V. T., *Discrepancy of trees*. Studia Sci.
  Math. Hungar. (1995), 47-57.
- [Zh11] Zhao, Yi, *Proof of the $(n/2-n/2-n/2)$ conjecture for large $n$*. Electron. J. Combin.
  (2011), Paper 27, 61.
-/

@[expose] public section

namespace Erdos580

/-- The number of vertices of `G` whose degree is at least `n / 2`. The halves are read in `ℚ`,
so for odd `n` this counts the vertices of degree at least $\lceil n/2 \rceil$. -/
noncomputable def numHighDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  {v : Fin n | ((n : ℚ) / 2) ≤ ((G.neighborSet v).ncard : ℚ)}.ncard

/--
Let $G$ be a graph on $n$ vertices such that at least $n/2$ vertices have degree at least $n/2$.
Must $G$ contain every tree on at most $n/2$ vertices?

A conjecture of Erdős, Füredi, Loebl, and Sós [EFLS95], the $(n/2-n/2-n/2)$ case of the
Loebl–Komlós–Sós conjecture. We follow erdosproblems.com in bounding the number of vertices of the
tree; [Zh11] bounds its number of edges by $n/2$, which gives a slightly stronger statement.
Containment is as a (not necessarily induced) subgraph.
-/
@[category research open, question, AMS 5]
theorem erdos_580 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ((n : ℚ) / 2) ≤ (numHighDegree G : ℚ) →
    ∀ (m : ℕ), (m : ℚ) ≤ (n : ℚ) / 2 →
    ∀ (T : SimpleGraph (Fin m)), T.IsTree → T.IsContained G := by
  sorry

/--
Zhao [Zh11] proved the conjecture for all sufficiently large $n$ (in the stronger form where the
tree has at most $n/2$ edges, which implies this one).
-/
@[category research solved, AMS 5]
theorem erdos_580.variants.zhao : ∀ᶠ n in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
    ((n : ℚ) / 2) ≤ (numHighDegree G : ℚ) →
    ∀ (m : ℕ), (m : ℚ) ≤ (n : ℚ) / 2 →
    ∀ (T : SimpleGraph (Fin m)), T.IsTree → T.IsContained G := by
  sorry

end Erdos580
