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
# The Birkhoff–Lewis conjecture on chromatic polynomials of planar graphs

For a finite simple graph $G = (V, E)$, the *chromatic polynomial* $P_G(x) \in \mathbb{R}[x]$ takes
at every integer $k \ge 0$ the number of proper $k$-colorings of $G$, and is given via Whitney's
subgraph expansion by
$$P_G(x) = \sum_{A \subseteq E} (-1)^{|A|} x^{c(V, A)},$$
where $c(V, A)$ counts the connected components of the spanning subgraph $(V, A)$. Birkhoff and
Lewis (1946) proved that $P_G(x) > 0$ for every finite planar graph $G$ and every real $x \ge 5$,
and conjectured that $P_G(x) > 0$ holds on all of $[4, \infty)$. At $x = 4$, $P_G(4) \ge 1$ is the
four-color theorem, while absence of real chromatic roots in $(4, 5)$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Chromatic_polynomial)
- [BL46] Birkhoff, G. D. and Lewis, D. C. (1946). *Chromatic polynomials*, Trans. Amer. Math. Soc.
  60, 355--451.
- [Tu95] Tutte, W. T. (1995). *Chromatic sums revisited*, Aequationes Math. 50 (1--2), 95--134.
-/

@[expose] public section

namespace BirkhoffLewisConjecture

/-- Spanning subgraph on `V` retaining only edges in $A \subseteq \operatorname{Sym2}(V)$. -/
def edgeSubsetGraph {V : Type*} (A : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ s(u, v) ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The empty edge subset defines the edgeless spanning subgraph $\bot$. -/
@[category API, AMS 5]
theorem edgeSubsetGraph_empty (V : Type*) : edgeSubsetGraph (∅ : Finset (Sym2 V)) = ⊥ := by
  ext u v
  simp [edgeSubsetGraph]

/-- **Chromatic polynomial** $P_G(X) \in \mathbb{R}[X]$ of a finite simple graph $G$, defined via
Whitney's subgraph-component expansion $\sum_{A \subseteq E(G)} (-1)^{|A|} X^{c(V, A)}$. -/
noncomputable def chromaticPolynomial {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Polynomial ℝ :=
  open scoped Classical in
  ∑ A ∈ G.edgeFinset.powerset,
    ((-1 : Polynomial ℝ) ^ A.card) *
      Polynomial.X ^ (Fintype.card (edgeSubsetGraph A).ConnectedComponent)

/-- On the edgeless graph $\bot$ on `Fin n`, Whitney's expansion has only $A = \emptyset$ with $n$
isolated components, so $P_{\bot}(X) = X^n$. -/
@[category API, AMS 5]
theorem chromaticPolynomial_bot_fin (n : ℕ) :
    chromaticPolynomial (⊥ : SimpleGraph (Fin n)) = Polynomial.X ^ n := by
  classical
  have hbij : Function.Bijective (⊥ : SimpleGraph (Fin n)).connectedComponentMk := by
    refine ⟨?_, fun c => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c⟩
    intro u v huv
    rcases SimpleGraph.ConnectedComponent.exact huv with ⟨w⟩
    cases w with
    | nil => rfl
    | cons hadj _ => exact False.elim hadj
  unfold chromaticPolynomial
  have hedge : ∀ (inst : Fintype (⊥ : SimpleGraph (Fin n)).edgeSet),
      @SimpleGraph.edgeFinset (Fin n) ⊥ inst = ∅ := by
    intro inst
    ext e
    simp
  rw [hedge, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero, one_mul,
    edgeSubsetGraph_empty]
  have hcard : ∀ (inst : Fintype (⊥ : SimpleGraph (Fin n)).ConnectedComponent),
      @Fintype.card (⊥ : SimpleGraph (Fin n)).ConnectedComponent inst = n :=
    fun inst =>
      (@Fintype.card_congr _ _ inst _ (Equiv.ofBijective _ hbij).symm).trans
        (Fintype.card_fin n)
  rw [hcard]

/-- On the $3$-vertex edgeless planar graph, $P_{\bot}(4) = 4^3 = 64 > 0$. -/
@[category test, AMS 5]
theorem chromaticPolynomial_bot_three_eval_four :
    (⊥ : SimpleGraph (Fin 3)).IsPlanar ∧
      (chromaticPolynomial (⊥ : SimpleGraph (Fin 3))).eval 4 = 64 := by
  refine ⟨SimpleGraph.isPlanar_bot, ?_⟩
  rw [chromaticPolynomial_bot_fin 3]
  norm_num

/--
**Birkhoff–Lewis conjecture** [BL46]: for every finite planar simple graph $G$ and every real
number $x \ge 4$, $P_G(x) > 0$ (in particular, $P_G$ has no real zeros in $(4, 5)$).
-/
@[category research open, AMS 5]
theorem birkhoff_lewis_conjecture {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsPlanar) (x : ℝ) (hx : 4 ≤ x) :
    0 < (chromaticPolynomial G).eval x := by
  sorry

/--
**Birkhoff–Lewis $[5, \infty)$ theorem** [BL46]: for every finite planar simple graph $G$ and every
real number $x \ge 5$, $P_G(x) > 0$.
-/
@[category research solved, AMS 5]
theorem birkhoff_lewis_conjecture.variants.five_le {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsPlanar) (x : ℝ) (hx : 5 ≤ x) :
    0 < (chromaticPolynomial G).eval x := by
  sorry

/--
**Four-color theorem in chromatic polynomial form**: for every finite planar simple graph $G$,
$P_G(4) \ge 1$.
-/
@[category research solved, AMS 5]
theorem birkhoff_lewis_conjecture.variants.four_color {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsPlanar) :
    1 ≤ (chromaticPolynomial G).eval 4 := by
  sorry

end BirkhoffLewisConjecture
