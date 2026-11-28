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
# Written on the Wall II - Conjecture 171

*References:*
- [E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), entry 171 (August 8, 2005).
- [takumayellow/math-autoresearch, Lower bounds for the spanning-tree leaf number (p0010)](https://github.com/takumayellow/math-autoresearch/tree/c24c95c4e0f706f5e236ad6b5bd68ca9a851710c/papers/p0010_wowii_ls_lower_bounds).

For a finite nontrivial connected simple graph $G$, let $L_s(G)$ denote the maximum number of
leaves over all spanning trees of $G$, let $\mathrm{distEven}(v)$ denote the number of vertices at
even distance from $v$, let $B(G) = \{v \mid \mathrm{ecc}(v) = \mathrm{diam}(G)\}$ denote the
periphery of $G$, and let $\mathrm{dist}_{\mathrm{avg}}(B(G))$ denote the mean distance over
distinct pairs of vertices in $B(G)$. Conjecture 171 proposed that
$$L_s(G) \ge \frac{\max_v \mathrm{distEven}(v) - 1}{\mathrm{dist}_{\mathrm{avg}}(B(G))}.$$

The conjecture is **false**, even for trees. Forming a tree $T$ of order $399$ from a root with
$26$ arms of length $14$ by attaching $1$ leaf at the end of the first arm, $33$ leaves at the end
of the second arm, and leaving the other $24$ arms unchanged gives diameter $30$, $L_s(T) = 58$,
$|B(T)| = 34$, and $\mathrm{dist}_{\mathrm{avg}}(B(T)) = 62/17$. Its odd-depth bipartition class
has size $216$, so $\max_v \mathrm{distEven}(v) = 216$ (and $215$ under the strictly positive
even-distance convention), whereas $(216 - 1) / (62 / 17) = 3655 / 62 > 58$ and
$(215 - 1) / (62 / 17) = 1819 / 31 > 58$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture171

open SimpleGraph

/-- The number of vertices at strictly positive even distance from $v$ in $G$. -/
noncomputable def distEvenPos {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun w => 0 < G.dist v w ∧ Even (G.dist v w)).card

/--
WOWII [Conjecture 171](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf):
does every finite nontrivial connected simple graph $G$ satisfy
$L_s(G) \ge (\max_v \mathrm{distEven}(v) - 1) / \mathrm{dist}_{\mathrm{avg}}(B(G))$,
where $B(G)$ is the periphery (`maxEccentricityVertices G`) and $\mathrm{distEven}(v)$ includes
$v$ itself at distance $0$?

This is false: a $399$-vertex tree has $L_s(T) = 58$, $\max_v \mathrm{distEven}(v) = 216$, and
$\mathrm{dist}_{\mathrm{avg}}(B(T)) = 62 / 17$, giving $(216 - 1) / (62 / 17) = 3655 / 62 > 58$.
The linked Palomar proof certifies the equivalent cross-multiplied inequality on this tree.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000009"]
theorem conjecture171 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        let maxDistEven := (Finset.univ.image (distEven G)).max' (by simp)
        ((maxDistEven : ℝ) - 1) / distAvgSet G (maxEccentricityVertices G) ≤ Ls G := by
  sorry

/--
Variant of WOWII Conjecture 171 counting only strictly positive even distances from $v$
($0 < \mathrm{dist}_G(v, w)$ and $2 \mid \mathrm{dist}_G(v, w)$). The same $399$-vertex tree
refutes this reading as well, giving $(215 - 1) / (62 / 17) = 1819 / 31 > 58 = L_s(T)$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000009"]
theorem conjecture171.variants.positive_even_distance :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        let maxDistEvenPos := (Finset.univ.image (distEvenPos G)).max' (by simp)
        ((maxDistEvenPos : ℝ) - 1) / distAvgSet G (maxEccentricityVertices G) ≤ Ls G := by
  sorry

-- Sanity checks

/-- `distEvenPos` is always nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 ≤ distEvenPos G v :=
  Nat.zero_le _

/-- In a complete graph, all distinct vertices are at distance $1$, so `distEvenPos` is $0$. -/
@[category test, AMS 5]
example : distEvenPos (⊤ : SimpleGraph (Fin 3)) 0 = 0 := by
  unfold distEvenPos
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_true_left,
    not_and]
  intro w hw
  have hne : (0 : Fin 3) ≠ w := fun h => by subst h; simp at hw
  have hd : (⊤ : SimpleGraph (Fin 3)).dist 0 w = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hne
  rw [hd]
  decide

end WrittenOnTheWallII.GraphConjecture171
