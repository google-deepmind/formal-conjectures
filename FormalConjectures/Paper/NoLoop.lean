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

# No Loop Conjectures

*References:*

Let $A$ be an Artin algebra over a commutative Artinian ring $R$.
The No Loop Conjectures are a family of statements relating $\operatorname{Ext}^1_A(S,S)$
for simple $A$-modules $S$ to homological properties of $S$ and $A$.

The *Extreme No Loop Conjecture* was formulated by S. Liu and J.-P. Morin in [The strong no loop conjecture for special biserial algebras,
Proc. Amer. Math. Soc. 132 (2004), 3513-3523](https://doi.org/10.1090/S0002-9939-04-07512-4).
It was also called Extension Conjecture later on.

The *Strong No Loop Conjecture* was solved for finite-dimensional algebras over algebraically closed fields
by K. Igusa, S. Liu and C. Paquette in
[A proof of the strong no loop conjecture](https://arxiv.org/abs/1103.5361),
published as [Adv. Math. 228 (2011), 2731-2742](https://doi.org/10.1016/j.aim.2011.06.042).

The *No Loop Conjecture* was solved assuming the same setup as above by K. Igusa
[Notes on the no loop conjecture, J. Pure Appl. Algebra 69 (1990), 161-176](https://doi.org/10.1016/0022-4049%2890%2990040-O).
In this setup,  the No Loop Conjecture follows also from earlier work of H. Lenzing
[Nilpotente Elemente in Ringen von endlicher globaler Dimension, Math. Z. 108 (1969), 313-324](https://doi.org/10.1007/BF01112536).

The three conjectures form successive strengthenings:
$$
\text{Extreme No Loop} \Longrightarrow \text{Strong No Loop}
\Longrightarrow \text{No Loop}.
$$

Remark:
We formulate the No Loop Conjectures in the form that non-vanishing of $\operatorname{Ext}^1(S,S)$ for a simple $A$-module $S$ leads to certain homological conditions.
If $A$ is isomorphic to a bound quiver algebra $kQ/I$, the vanishing of $\operatorname{Ext}^1_A(S,S)$ for all simple $A$-modules $S$ corresponds to the absence of loops in the quiver.
In particular, the contrapositives of our formulations justify the 'No Loops'-terminology assuming the quiver description of $A$.
-/

open CategoryTheory Abelian Limits

universe u v w

namespace NoLoopConjectures

/-
Let `R` be a commutative Artinian ring, `A` a module-finite `R`-algebra and `S` a simple module over `A` so that `Ext^1(S,S) ≠ 0` -/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A]
variable [Algebra R A] [Module.Finite R A] (S : ModuleCat.{v} A) [Simple S]

abbrev ext1_neq_zero := ¬ Subsingleton (Ext S S 1)

variable (A) in
abbrev infinite_global_dim_statement := ∀ n:ℕ , ∃ M : ModuleCat.{v} A, projectiveDimension M > n

abbrev no_loop_statement := ext1_neq_zero S  →  infinite_global_dim_statement A

include R in
/--
The *No Loop Conjecture*:
For any simple $A$-module $S$
$$
\operatorname{Ext}^1_A(S,S) \neq 0
\quad \Longrightarrow  \quad
\operatorname{gldim} A = \infty
$$
-/
@[category research open, AMS 16 18]
theorem no_loop : no_loop_statement S := by
  sorry

abbrev strong_no_loop_statement := ext1_neq_zero S  → projectiveDimension S = ⊤

include R in
/--
The *Strong No Loop Conjecture*:
For any simple $A$-module $S$
$$
\operatorname{Ext}^1_A(S,S) \neq 0
\quad \Longrightarrow  \quad
\operatorname{prdim} S = \infty
$$
-/
@[category research open, AMS 16 18]
theorem strong_no_loop : strong_no_loop_statement S := by
  sorry

/--
The *Strong No Loop Conjecture* was solved for finite-dimensional algebras over algebraically closed fields
by K. Igusa, S. Liu and C. Paquette in
[A proof of the strong no loop conjecture](https://arxiv.org/abs/1103.5361)
-/
@[category research solved, AMS 16 18]
theorem strong_no_loop_alg_closed {k : Type u} [Field k] [IsAlgClosed k] [Algebra k A] [Module.Finite k A] : strong_no_loop_statement S := by
  sorry

abbrev extreme_no_loop_statement := ext1_neq_zero S → ∀ i, ∃ n > i,¬ Subsingleton (Ext S S n)

include R in
/--
The *Extreme No Loop Conjecture*:
For any simple $A$-module $S$
$$
\operatorname{Ext}^1_A(S,S) \neq   0
\quad \Longrightarrow  \quad
\operatorname{Ext}^i_A(S,S) \neq 0
\text{ for infinitely many }i > 0
$$
-/
@[category research open, AMS 16 18]
theorem extreme_no_loop : extreme_no_loop_statement S:= by
  sorry

/--
The Extreme No Loop Conjecture implies the Strong No Loop Conjecture.
-/
@[category test, AMS 16 18]
lemma extreme_imply_strong: (∀ S: ModuleCat A, Module.Finite A S → Simple S → extreme_no_loop_statement S ) → (∀ S: ModuleCat A, Module.Finite A S → Simple S → strong_no_loop_statement S ) := by
  intro h S fS sS neZS
  by_contra!
  rcases (projectiveDimension_ne_top_iff _ ).1 this with ⟨m,hm⟩
  rcases h S fS sS neZS m with ⟨n,hn⟩
  exact hn.2 <| (HasProjectiveDimensionLT.subsingleton (hX := hm) _ ) _ (Nat.succ_le_of_lt hn.1) _

/--
The Strong No Loop Conjecture implies the No Loop Conjecture.
-/
@[category test, AMS 16 18]
lemma strong_imply_normal: (∀ S: ModuleCat A, Simple S → strong_no_loop_statement S ) → (∀ S: ModuleCat A, Simple S → no_loop_statement S) := fun  h S sS neZS n => ⟨S,by
  rw [ h S sS neZS]
  exact WithBot.LT.coe_lt_coe <| ENat.natCast_lt_top n⟩

/--
Use strong_imply_normal and the special case of the strong no loop conjecture to prove a special case of the no loop conjecture
-/
@[category test, AMS 16 18]
lemma no_loop_alg_closed {k : Type u} [Field k] [IsAlgClosed k] [Algebra k A] [Module.Finite k A] :  no_loop_statement S := strong_imply_normal
  (fun S _ => strong_no_loop_alg_closed (k := k) S) S (by infer_instance)


end NoLoopConjectures
