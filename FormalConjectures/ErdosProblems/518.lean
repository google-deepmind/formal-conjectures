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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 518

*References:*
- [erdosproblems.com/518](https://www.erdosproblems.com/518)
- [ErGy95] Erdős, Paul and Gyárfás, András, _Vertex covering with monochromatic paths_. Math.
  Pannon. (1995), 7--10.
- [GeGy67] Gerencsér, L. and Gyárfás, A., _On Ramsey-type problems_. Ann. Univ. Sci. Budapest.
  Eötvös Sect. Math. (1967), 167--170.
- [PVW24] A. Pokrovskiy, L. Versteegen, and E. Williams, _A proof of a conjecture of Erdős and
  Gyárfás on monochromatic path covers_. arXiv:2409.03623 (2024).
-/

@[expose] public section

namespace Erdos518

variable {V : Type*}

/-- The vertices of `G` can be covered by at most `k` paths of `G`. The paths are not required to
be vertex-disjoint, and a single vertex counts as a path. -/
def HasPathCover (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (P : Fin m → (u : V) × (v : V) × G.Walk u v), m ≤ k ∧
    (∀ i, (P i).2.2.IsPath) ∧ ∀ x : V, ∃ i, x ∈ (P i).2.2.support

/--
Is it true that, in any two-colouring of the edges of $K_n$, there exist $\sqrt{n}$ monochromatic
paths, all of the same colour, which cover all vertices?

A two-colouring of the edges of $K_n$ is represented by a graph `G` on `Fin n`: the edges of `G`
are the red edges and those of `Gᶜ` the blue ones.

The answer is yes, proved by Pokrovskiy, Versteegen, and Williams [PVW24]. Erdős and Gyárfás
[ErGy95] proved that $2\sqrt{n}$ paths suffice, and observed that $\sqrt{n}$ would be best
possible.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos518.lean#L34"]
theorem erdos_518 : answer(True) ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasPathCover G (Nat.sqrt n) ∨ HasPathCover Gᶜ (Nat.sqrt n) := by
  sorry

/--
Gerencsér and Gyárfás [GeGy67] proved that, if the paths do not need to be of the same colour,
then two paths suffice: the vertices of $K_n$ can be covered by a path of one colour and a path
of the other colour.
-/
@[category research solved, AMS 5]
theorem erdos_518.variants.gerencser_gyarfas (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ (u v : Fin n) (p : G.Walk u v) (u' v' : Fin n) (q : Gᶜ.Walk u' v'),
      p.IsPath ∧ q.IsPath ∧ ∀ x, x ∈ p.support ∨ x ∈ q.support := by
  sorry

/-- Erdős and Gyárfás [ErGy95] proved that $2\sqrt{n}$ paths suffice. -/
@[category research solved, AMS 5]
theorem erdos_518.variants.erdos_gyarfas (n : ℕ) (G : SimpleGraph (Fin n)) :
    HasPathCover G (2 * Nat.sqrt n) ∨ HasPathCover Gᶜ (2 * Nat.sqrt n) := by
  sorry

end Erdos518
