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
# Erdős Problem 609

*References:*
- [erdosproblems.com/609](https://www.erdosproblems.com/609)
- [ErGr75] Erdős, P. and Graham, R. L., On partition theorems for finite graphs.
  Colloq. Math. Soc. János Bolyai (1975).
- [Ch97] Chung, F., Open problems of Paul Erdős in graph theory. J. Graph Theory (1997), 3-36.
- [DaJo17] Day, A. N. and Johnson, J. R., Multicolour Ramsey numbers of odd cycles.
  J. Combin. Theory Ser. B (2017), 56-63.
- [GiHu24] Girão, A. and Hunter, Z., Multicolour Ramsey numbers of odd cycles.
  arXiv:2404.05441 (2024).
- [JaYi25] Janzer, O. and Yip, C. H., Multicolour Ramsey numbers of odd cycles.
  arXiv:2501.05432 (2025).
-/

open Filter

namespace Erdos609

/--
The monochromatic subgraph of color `i` under edge coloring `c : Sym2 V → Fin n`.
-/
def monochromaticGraph {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v ↦ c s(u, v) = i)

/--
A coloring `c` has a monochromatic odd cycle of length at most `m`.
-/
def MonochromaticHasOddCycleLe (n : ℕ) (m : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) : Prop :=
  ∃ (i : Fin n) (l : ℕ), l ∈ (monochromaticGraph c i).oddCycleLengths ∧ l ≤ m

/--
$f(n)$ is the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured with $n$ colours
then there must be a monochromatic odd cycle of length at most $m$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (c : Sym2 (Fin (2 ^ n + 1)) → Fin n), MonochromaticHasOddCycleLe n m c}

/--
Let $f(n)$ be the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured with $n$ colours
then there must be a monochromatic odd cycle of length at most $m$. Estimate $f(n)$.
-/
@[category research open, AMS 5]
theorem erdos_609 :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos609
