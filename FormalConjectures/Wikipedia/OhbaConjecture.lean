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
# Ohba's conjecture (2002; proved by Noel, Reed and Wu 2015)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/List_coloring#Ohba's_conjecture)
* [Oh02] Ohba, K. (2002). "On chromatic-choosable graphs." *J. Graph Theory* 40, pp. 130--135.
* [NRW15] Noel, J. A., Reed, B. A. and Wu, H. (2015). "A proof of a conjecture of Ohba."
  *J. Graph Theory* 79, pp. 86--102. [arXiv:1211.1999](https://arxiv.org/abs/1211.1999)
* [ERT79] Erdős, P., Rubin, A. L. and Taylor, H. (1979). "Choosability in graphs."
  *Congr. Numer.* 26, pp. 125--157.
-/

open SimpleGraph Finset

namespace OhbaConjecture

variable {V : Type*}

/-- `G` is **`k`-choosable** if for every assignment `L` of a list of `k` colours to each
vertex there is a proper colouring `c` with `c v ∈ L v` for all `v`. -/
def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- The **choice number** (list chromatic number) `ch(G)`: the least `k` for which `G` is
`k`-choosable. -/
noncomputable def choiceNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | Choosable G k}

/--
**Ohba's conjecture (2002), proved by Noel, Reed and Wu (2015).**

Every graph $G$ with at most $2\chi(G) + 1$ vertices is *chromatic-choosable*: it is
$\chi(G)$-choosable, so its choice number equals its chromatic number.
-/
@[category research solved, AMS 5]
theorem ohba_conjecture : answer(True) ↔
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (Fintype.card V : ℕ∞) ≤ 2 * G.chromaticNumber + 1 →
      Choosable G G.chromaticNumber.toNat := by
  sorry

/--
**Complete multipartite graphs with parts of size at most $2$ (Erdős–Rubin–Taylor 1979).**

Ohba's conjecture is sharp: the complete multipartite graph $K_{2,2,\dots,2}$ with $k$ parts
has $2k$ vertices and is $k$-choosable, while adding a further vertex to a part of size $2$ can
break chromatic-choosability. Erdős, Rubin and Taylor showed $K_{2,\dots,2}$ is
$k$-choosable.

*Reference:* [ERT79].
-/
@[category research solved, AMS 5]
theorem ohba_conjecture.variants.erdos_rubin_taylor (k : ℕ) :
    Choosable (completeMultipartiteGraph (fun _ : Fin k => Fin 2)) k := by
  sorry

/-- A `k`-choosable graph is `k`-colourable (take the constant list `{0, …, k-1}`). -/
@[category API, AMS 5]
lemma Choosable.colorable {G : SimpleGraph V} {k : ℕ} (h : Choosable G k) : G.Colorable k := by
  obtain ⟨c, hc, hadj⟩ := h (fun _ => Finset.range k) (fun _ => Finset.card_range k)
  refine ⟨⟨fun v => ⟨c v, Finset.mem_range.mp (hc v)⟩, fun {u v} huv h => hadj u v huv ?_⟩⟩
  exact congrArg Fin.val h

/--
**Chromatic-choosability implies the trivial direction: `χ(G) ≤ ch(G)` always.**

Every `k`-choosable graph is `k`-colourable, so the chromatic number never exceeds the choice
number. Ohba's conjecture is the statement that equality holds for small graphs.
-/
@[category API, AMS 5]
theorem chromaticNumber_le_choiceNumber [Fintype V] (G : SimpleGraph V)
    (h : ∃ k, Choosable G k) : G.chromaticNumber ≤ choiceNumber G :=
  (Choosable.colorable (G := G) (Nat.sInf_mem h)).chromaticNumber_le

end OhbaConjecture
