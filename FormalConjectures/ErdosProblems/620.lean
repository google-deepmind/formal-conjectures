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
# Erdős Problem 620

*References:*
- [erdosproblems.com/620](https://www.erdosproblems.com/620)
- [BoHi91] Bollobás, B. and Hind, H. R., *Graphs without large triangle free subgraphs*.
  Discrete Math. (1991), 119-131.
- [ErRo62] Erdős, P. and Rogers, C. A., *The construction of certain graphs*.
  Canadian J. Math. (1962), 702-707.
- [MSV26] Morris, R., Sahasrabudhe, J. and Verstraëte, J., *On the Erdős–Rogers function*.
  arXiv:2607.16118 (2026).
- [MuVe24] Mubayi, D. and Verstraëte, J., *On the order of the classical Erdős–Rogers functions*.
  Bull. London Math. Soc. (2025). arXiv:2401.02548.
- [Sh95] Shearer, J. B., *On the independence number of sparse graphs*.
  Random Structures Algorithms (1995), 269-271.
- [Wo13] Wolfovitz, G., *$K_4$-free graphs without large induced triangle-free subgraphs*.
  Combinatorica (2013), 623-631.
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos620

/-- The maximum number of vertices of an induced triangle-free subgraph of `G` -- that is, the
largest size of a vertex set of `G` spanning no triangle. -/
noncomputable def triangleFreeNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.powerset.filter
    (fun S : Finset V => G.CliqueFreeOn (S : Set V) 3)).sup Finset.card

/-- `f n` is the largest `m` such that every $K_4$-free graph on `n` vertices contains an
induced triangle-free subgraph on `m` vertices. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧ triangleFreeNumber G = k}

/-- Sanity check: `triangleFreeNumber G` is at most the number of vertices of `G`. -/
@[category API, AMS 5]
theorem triangleFreeNumber_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    triangleFreeNumber G ≤ Fintype.card V := by
  classical
  unfold triangleFreeNumber
  apply Finset.sup_le
  intro S _
  simpa using Finset.card_le_card (Finset.subset_univ S)

/-- Any triangle-free vertex set is a lower bound for `triangleFreeNumber`. -/
@[category API, AMS 5]
theorem card_le_triangleFreeNumber {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (hS : G.CliqueFreeOn (S : Set V) 3) : S.card ≤ triangleFreeNumber G := by
  classical
  unfold triangleFreeNumber
  exact Finset.le_sup (f := Finset.card) (by simpa using hS)

/-- Sanity check: `f n ≤ n`, witnessed by the empty graph, which is $K_4$-free. -/
@[category test, AMS 5]
theorem f_le (n : ℕ) : f n ≤ n := by
  calc f n ≤ triangleFreeNumber (⊥ : SimpleGraph (Fin n)) :=
        Nat.sInf_le ⟨⊥, SimpleGraph.cliqueFree_bot (by norm_num), rfl⟩
    _ ≤ n := by simpa using triangleFreeNumber_le_card (⊥ : SimpleGraph (Fin n))

/-- Sanity check: `f 3 = 2`. The triangle $K_3$ is $K_4$-free and its only 3-vertex set is a
triangle, while any two vertices span no triangle. Unlike `f_le`, this depends on both clique
sizes in the definitions: with `CliqueFreeOn _ 2` it would be `1`, and with `CliqueFree 3` it
would be `3`. -/
@[category test, AMS 5]
theorem f_three : f 3 = 2 := by
  classical
  apply le_antisymm
  · calc f 3 ≤ triangleFreeNumber (⊤ : SimpleGraph (Fin 3)) :=
          Nat.sInf_le ⟨⊤, SimpleGraph.cliqueFree_of_card_lt (by simp), rfl⟩
      _ ≤ 2 := by
          unfold triangleFreeNumber
          apply Finset.sup_le
          intro S hS
          by_contra! h
          have hcard : S.card = Fintype.card (Fin 3) := by
            have := Finset.card_le_univ S
            simp only [Fintype.card_fin] at this ⊢
            omega
          obtain rfl := Finset.eq_univ_of_card S hcard
          have hK : (⊤ : SimpleGraph (Fin 3)).IsNClique 3 Finset.univ :=
            ⟨SimpleGraph.IsClique.top _, by simp⟩
          exact (Finset.mem_filter.mp hS).2 (Set.Subset.refl _) hK
  · unfold f
    refine le_csInf ⟨_, ⊥, SimpleGraph.cliqueFree_bot (by norm_num), rfl⟩ ?_
    rintro k ⟨G, -, rfl⟩
    have h := card_le_triangleFreeNumber G ({0, 1} : Finset (Fin 3))
      (SimpleGraph.cliqueFreeOn_of_card_lt G (by decide))
    have h2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    rwa [h2] at h

/-- The order of growth of `f`. -/
def erdos_620.answer : ℕ → ℝ := sorry

/--
How large must the largest induced triangle-free subgraph of a $K_4$-free graph on $n$
vertices be? Determine the order of growth of $f(n)$.

Morris, Sahasrabudhe and Verstraëte [MSV26] claim $f(n) = \Theta(\sqrt{n \log n})$. This is a
preprint and erdosproblems.com still lists the problem as open, so it is recorded as
open here.
-/
@[category research open, question value, AMS 5]
theorem erdos_620 : (fun n : ℕ => (f n : ℝ)) =Θ[atTop] erdos_620.answer := by
  sorry

/--
The best known lower bound from Shearer [Sh95]:
$f(n) \gg n^{1/2} (\log n)^{1/2} / \log \log n$.
Earlier, Bollobás and Hind [BoHi91] proved $f(n) \gg n^{1/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_620.variants.lower_shearer :
    (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log n) / Real.log (Real.log n)) ≪
      (fun n : ℕ => (f n : ℝ)) := by
  sorry

/--
The best known upper bound from Mubayi and Verstraëte [MuVe24]:
$f(n) \ll n^{1/2} \log n$.
This improves Wolfovitz's $f(n) \ll n^{1/2} (\log n)^{120}$ [Wo13], which in turn improved
Bollobás and Hind's $f(n) \ll n^{7/10 + o(1)}$ [BoHi91].
-/
@[category research solved, AMS 5]
theorem erdos_620.variants.upper_mubayi_verstraete :
    (fun n : ℕ => (f n : ℝ)) ≪ (fun n : ℕ => Real.sqrt n * Real.log n) := by
  sorry

/--
$f(n) = n^{1/2 + o(1)}$, which follows from the two bounds above. Formally, and weaker than
them: for every $\varepsilon > 0$, $n^{1/2 - \varepsilon} \le f(n) \le n^{1/2 + \varepsilon}$
for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_620.variants.exponent_half :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

end Erdos620
