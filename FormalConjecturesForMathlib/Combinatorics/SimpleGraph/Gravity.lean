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

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The gravity matrix of a graph

The gravity matrix of a finite graph $G$ on $n$ vertices has entry $0$ on the diagonal and
$\frac{d(u) d(v)}{(n - 1) \operatorname{dist}(u, v)}$ at $(u, v)$ for $u \ne v$. The entry is
also $0$ when no path joins $u$ and $v$.

*References:*
- S. Fajtlowicz, *Written on the Wall* (July 2004 version), p. 52.
- T. L. Brewster, M. J. Dinneen and V. Faber, *A computational attack on the conjectures of
  Graffiti: new counterexamples and proofs*, Discrete Math. 147 (1995), 35–55.

The source does not define the mean of a matrix. `meanGravity` is the mean of all $n^2$
entries and `meanGravityOffDiagonal` is the mean of the $n(n-1)$ off-diagonal entries.
-/

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The gravity matrix of `G`. The $(u, v)$ entry is $0$ if $u = v$, and otherwise
$\frac{d(u) d(v)}{(n - 1) \operatorname{dist}(u, v)}$, where $n$ is the number of vertices.
If no path joins $u$ and $v$, then `G.dist u v = 0` and the entry is $0$, as in the source. -/
noncomputable def gravity (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℝ :=
  if u = v then 0
  else (G.degree u * G.degree v : ℝ) / ((Fintype.card α - 1 : ℝ) * G.dist u v)

/-- The mean of the $n^2$ entries of the gravity matrix of `G`. -/
noncomputable def meanGravity (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, G.gravity u v) / (Fintype.card α : ℝ) ^ 2

/-- The mean of the $n(n-1)$ off-diagonal entries of the gravity matrix of `G`. -/
noncomputable def meanGravityOffDiagonal (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, G.gravity u v) / (Fintype.card α * (Fintype.card α - 1) : ℝ)

variable (G : SimpleGraph α) [DecidableRel G.Adj]

@[simp]
lemma gravity_self (u : α) : G.gravity u u = 0 := by
  simp [gravity]

lemma gravity_comm (u v : α) : G.gravity u v = G.gravity v u := by
  unfold gravity
  by_cases h : u = v
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), mul_comm (G.degree u : ℝ), dist_comm]

lemma gravity_nonneg (u v : α) : 0 ≤ G.gravity u v := by
  unfold gravity
  split_ifs with h
  · exact le_rfl
  · have hn : (1 : ℝ) < Fintype.card α := by
      exact_mod_cast Fintype.one_lt_card_iff.mpr ⟨u, v, h⟩
    exact div_nonneg (by positivity) (mul_nonneg (by linarith) (Nat.cast_nonneg _))

lemma meanGravity_nonneg : 0 ≤ G.meanGravity :=
  div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.gravity_nonneg u v)
    (by positivity)

/-- For $K_2$, each off-diagonal entry of the gravity matrix is $1$, so the mean of the four
entries is $1/2$. This checks the $(n - 1)$ factor and the $n^2$ normalisation. -/
example : (⊤ : SimpleGraph (Fin 2)).meanGravity = 1 / 2 := by
  have h01 : (⊤ : SimpleGraph (Fin 2)).dist 0 1 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  have h10 : (⊤ : SimpleGraph (Fin 2)).dist 1 0 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  simp [meanGravity, gravity, Fin.sum_univ_two, h01, h10, complete_graph_degree]
  norm_num

/-- For $K_2$, the two off-diagonal entries are $1$, so their mean is $1$. -/
example : (⊤ : SimpleGraph (Fin 2)).meanGravityOffDiagonal = 1 := by
  have h01 : (⊤ : SimpleGraph (Fin 2)).dist 0 1 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  have h10 : (⊤ : SimpleGraph (Fin 2)).dist 1 0 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  simp [meanGravityOffDiagonal, gravity, Fin.sum_univ_two, h01, h10, complete_graph_degree]
  norm_num

end SimpleGraph
