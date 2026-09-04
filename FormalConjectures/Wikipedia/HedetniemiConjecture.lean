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
# Hedetniemi's conjecture (1966)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Hedetniemi%27s_conjecture)
* [He66] Hedetniemi, S. T. (1966). *Homomorphisms of graphs and automata.* Technical Report
  03105-44-T, University of Michigan.
* [ES85] El-Zahar, M. and Sauer, N. (1985). "The chromatic number of the product of two
  4-chromatic graphs is 4." *Combinatorica* 5, pp. 121--126.
* [Sh19] Shitov, Y. (2019). "Counterexamples to Hedetniemi's conjecture." *Ann. of Math.* 190,
  pp. 663--667. [arXiv:1905.02167](https://arxiv.org/abs/1905.02167)
* [Ta22] Tardif, C. (2022). "The chromatic number of the product of 14-chromatic graphs can
  be 13." *Combinatorica* 42, pp. 301--308.
* [Zh21] Zhu, X. (2021). "Relatively small counterexamples to Hedetniemi's conjecture."
  *J. Combin. Theory Ser. B* 146, pp. 141--150.
-/

open SimpleGraph

namespace HedetniemiConjecture

variable {α β : Type*}

/-- The **tensor (categorical) product** `G × H` of two simple graphs: `(a, b)` and `(c, d)` are
adjacent iff `a ~ c` in `G` and `b ~ d` in `H`. -/
def tensorProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- The projection `G × H →g G` onto the first factor. -/
def tensorProd.fst (G : SimpleGraph α) (H : SimpleGraph β) : tensorProd G H →g G :=
  ⟨Prod.fst, fun h => h.1⟩

/-- The projection `G × H →g H` onto the second factor. -/
def tensorProd.snd (G : SimpleGraph α) (H : SimpleGraph β) : tensorProd G H →g H :=
  ⟨Prod.snd, fun h => h.2⟩

/--
**Hedetniemi's conjecture (1966) — disproved.**

For all finite simple graphs $G$ and $H$, the chromatic number of the tensor product was
conjectured to satisfy $\chi(G \times H) = \min\{\chi(G), \chi(H)\}$.

This is **false**: Shitov [Sh19] constructed finite graphs $G$, $H$ with
$\chi(G \times H) < \min\{\chi(G), \chi(H)\}$. The inequality $\le$ always holds
(`chromaticNumber_tensorProd_le_min`); it is the reverse inequality that fails.
-/
@[category research solved, AMS 5]
theorem hedetniemi_conjecture : answer(False) ↔
    ∀ {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β),
      (tensorProd G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber := by
  sorry

/--
**The easy inequality: `χ(G × H) ≤ min {χ(G), χ(H)}`.**

Any colouring of `G` (resp. `H`) pulls back along the projection `G × H →g G` (resp. `H`) to a
colouring of `G × H`.
-/
@[category API, AMS 5]
theorem chromaticNumber_tensorProd_le_min (G : SimpleGraph α) (H : SimpleGraph β) :
    (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber := by
  refine le_min ?_ ?_
  · exact chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom (tensorProd.fst G H)
  · exact chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom (tensorProd.snd G H)

/--
**El-Zahar–Sauer (1985): the conjecture holds when `min {χ(G), χ(H)} ≤ 4`.**

If both $G$ and $H$ are $4$-chromatic then so is $G \times H$; together with the easy cases
$\min\{\chi(G), \chi(H)\} \le 3$, this gives Hedetniemi's equality whenever
$\min\{\chi(G), \chi(H)\} \le 4$.

*Reference:* [ES85].
-/
@[category research solved, AMS 5]
theorem hedetniemi_conjecture.variants.el_zahar_sauer
    {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
    (h : min G.chromaticNumber H.chromaticNumber ≤ 4) :
    (tensorProd G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber := by
  sorry

/--
**Shitov (2019): the conjecture fails.**

There exist finite graphs $G$, $H$ with $\chi(G \times H) < \min\{\chi(G), \chi(H)\}$.
Tardif [Ta22] later gave counterexamples with $\min\{\chi(G),\chi(H)\} = 14$ and
$\chi(G \times H) = 13$, and Zhu [Zh21] considerably smaller ones.

*References:* [Sh19], [Ta22], [Zh21].
-/
@[category research solved, AMS 5]
theorem hedetniemi_conjecture.variants.shitov :
    ∃ (α β : Type) (_ : Fintype α) (_ : Fintype β) (G : SimpleGraph α) (H : SimpleGraph β),
      (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber := by
  sorry

end HedetniemiConjecture
