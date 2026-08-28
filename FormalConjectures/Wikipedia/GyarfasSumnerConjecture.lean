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
# The Gyárfás–Sumner conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Gy%C3%A1rf%C3%A1s%E2%80%93Sumner_conjecture)
* [Gy75] Gyárfás, A. (1975). "On Ramsey covering-numbers." *Infinite and finite sets*,
  Colloq. Math. Soc. János Bolyai 10, pp. 801--816.
* [Su81] Sumner, D. P. (1981). "Subtrees of a graph and the chromatic number." *The theory
  and applications of graphs (Kalamazoo, 1980)*, Wiley, pp. 557--576.
* [Gy87] Gyárfás, A. (1987). "Problems from the world surrounding perfect graphs."
  *Zastos. Mat.* 19, pp. 413--441.
* [KP94] Kierstead, H. A. and Penrice, S. G. (1994). "Radius two trees specify χ-bounded
  classes." *J. Graph Theory* 18, pp. 119--129.
* [SS20] Scott, A. and Seymour, P. (2020). "A survey of χ-boundedness." *J. Graph Theory* 95,
  pp. 473--504. [arXiv:1812.07500](https://arxiv.org/abs/1812.07500)
-/

open SimpleGraph

namespace GyarfasSumnerConjecture

/-- A class of graphs given by a forbidden induced subgraph `T` is **χ-bounded by `f`** if every
finite graph `G` with no induced copy of `T` satisfies `χ(G) ≤ f(ω(G))`. -/
def IsChiBoundedBy {W : Type} (T : SimpleGraph W) (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ SimpleGraph.IsIndContained T G → G.chromaticNumber ≤ f G.cliqueNum

/--
**The Gyárfás–Sumner conjecture (Gyárfás 1975, Sumner 1981).**

For every finite tree $T$ the class of $T$-free graphs (graphs with no induced subgraph
isomorphic to $T$) is $\chi$-bounded: there is a function $f$ such that every $T$-free graph
$G$ satisfies $\chi(G) \le f(\omega(G))$.
-/
@[category research open, AMS 5]
theorem gyarfas_sumner_conjecture : answer(sorry) ↔
    ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
      T.IsTree → ∃ f : ℕ → ℕ, IsChiBoundedBy T f := by
  sorry

/--
**Paths (Gyárfás 1987).**

For every $n$, the class of $P_n$-free graphs is $\chi$-bounded; Gyárfás's argument gives
$\chi(G) \le (n-1)^{\omega(G) - 1}$.

*Reference:* [Gy87].
-/
@[category research solved, AMS 5]
theorem gyarfas_sumner_conjecture.variants.path (n : ℕ) :
    ∃ f : ℕ → ℕ, IsChiBoundedBy (pathGraph n) f := by
  sorry

/--
**Trees of radius two (Kierstead–Penrice 1994).**

Every tree of radius at most $2$ (i.e. with a vertex within distance $2$ of every other vertex)
specifies a $\chi$-bounded class.

*Reference:* [KP94].
-/
@[category research solved, AMS 5]
theorem gyarfas_sumner_conjecture.variants.radius_two
    {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsTree) (hrad : ∃ c : W, ∀ w : W, T.dist c w ≤ 2) :
    ∃ f : ℕ → ℕ, IsChiBoundedBy T f := by
  sorry

/--
**The conjecture is trivial when `T` is a single vertex.**

If $T$ is a single vertex then every nonempty graph contains an induced copy of $T$, so the
only $T$-free graph is the empty graph, whose chromatic number is $0$; hence
$f = 0$ works.
-/
@[category research solved, AMS 5]
theorem gyarfas_sumner_conjecture.variants.singleton :
    IsChiBoundedBy (⊥ : SimpleGraph (Fin 1)) (fun _ => 0) := by
  intro V _ _ G _ hT
  -- `G` has no vertices: otherwise the single vertex embeds into `G`.
  have hV : IsEmpty V := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨v⟩ := h
    exact hT ⟨⟨⟨fun _ => v, fun _ _ _ => Subsingleton.elim _ _⟩, fun {a b} => by
      simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]⟩⟩
  simp

end GyarfasSumnerConjecture
