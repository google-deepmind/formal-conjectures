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
# Erdős Problem 808

*References:*
- [erdosproblems.com/808](https://www.erdosproblems.com/808)
- [ErSz83] Erdős, P. and Szemerédi, E., *On sums and products of integers*. Studies in pure
  mathematics (1983), 213-218. [PDF](https://www.renyi.hu/~p_erdos/1983-18.pdf)
- [ARS20] Alon, Noga and Ruzsa, Imre and Solymosi, József, *Sums, products and ratios along the
  edges of a graph*. Publ. Mat. (2020), 143-155.
  [arXiv:1802.06405](https://arxiv.org/abs/1802.06405)
-/

@[expose] public section

namespace Erdos808

/-- The values of the symmetric operation `op` along the edges of the graph `G`: the set of all
`op u v` with `{u, v}` an edge of `G`. -/
def edgeValues {V R : Type*} [Fintype V] [DecidableEq R]
    (op : V → V → R) (hop : ∀ u v, op u v = op v u)
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  G.edgeFinset.image (Sym2.lift ⟨op, hop⟩)

/-- `edgeSums a G` is $A +_G A = \{ a_u + a_v : \{u, v\} \in E(G) \}$, where vertex `u` of `G`
carries the label `a u`. -/
def edgeSums {V R : Type*} [Fintype V] [DecidableEq R] [AddCommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u + a v) (fun u v ↦ add_comm (a u) (a v)) G

/-- `edgeProducts a G` is $A \cdot_G A = \{ a_u a_v : \{u, v\} \in E(G) \}$. -/
def edgeProducts {V R : Type*} [Fintype V] [DecidableEq R] [CommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u * a v) (fun u v ↦ mul_comm (a u) (a v)) G

/-- `r` is a value of `op` along an edge iff `r = op u v` for some adjacent `u`, `v`. -/
@[category API, AMS 5 11]
theorem mem_edgeValues_iff {V R : Type*} [Fintype V] [DecidableEq R]
    (op : V → V → R) (hop : ∀ u v, op u v = op v u)
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : R) :
    r ∈ edgeValues op hop G ↔ ∃ u v, G.Adj u v ∧ r = op u v := by
  constructor
  · intro hr
    obtain ⟨e, he, her⟩ := Finset.mem_image.mp hr
    induction e using Sym2.inductionOn with
    | _ u v =>
        refine ⟨u, v, ?_, ?_⟩
        · simpa using he
        · simpa [Sym2.lift_mk] using her.symm
  · rintro ⟨u, v, huv, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨s(u, v), ?_, by simp [Sym2.lift_mk]⟩
    simpa

/-- `r ∈ A +_G A` iff `r = a u + a v` for some adjacent `u`, `v`. -/
@[category API, AMS 5 11]
theorem mem_edgeSums_iff {V R : Type*} [Fintype V] [DecidableEq R] [AddCommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] (r : R) :
    r ∈ edgeSums a G ↔ ∃ u v, G.Adj u v ∧ r = a u + a v :=
  mem_edgeValues_iff (fun u v ↦ a u + a v) (fun u v ↦ add_comm (a u) (a v)) G r

/-- `r ∈ A ·_G A` iff `r = a u * a v` for some adjacent `u`, `v`. -/
@[category API, AMS 5 11]
theorem mem_edgeProducts_iff {V R : Type*} [Fintype V] [DecidableEq R] [CommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] (r : R) :
    r ∈ edgeProducts a G ↔ ∃ u v, G.Adj u v ∧ r = a u * a v :=
  mem_edgeValues_iff (fun u v ↦ a u * a v) (fun u v ↦ mul_comm (a u) (a v)) G r

set_option linter.style.formal_proof_palomar false in
/--
Let $c,\epsilon>0$ and $n$ be sufficiently large. If $A\subset \mathbb{N}$ has $\lvert A\rvert=n$
and $G$ is any graph on $A$ with at least $n^{1+c}$ edges then
$$\max(\lvert A+_GA\rvert,\lvert A\cdot_G A\rvert) \geq \lvert A\rvert^{1+c-\epsilon},$$
where
$$A+_GA = \{ a+b : (a,b)\in G\}$$
and similarly for $A\cdot_GA$.

This strong conjecture of Erdős and Szemerédi [ErSz83] strengthens Erdős Problem 52
(`Erdos52.erdos_52`, the case of the complete graph). It was disproved by Alon, Ruzsa, and
Solymosi [ARS20, Theorem 3]: for arbitrarily large $m$ there are a set of integers $A$ with
$\lvert A\rvert=m$ and a graph on $A$ with $\gg m^{5/3}/(\log m)^{1/3}$ edges such that
$\lvert A+_GA\rvert+\lvert A\cdot_GA\rvert \ll (m\log m)^{4/3}$. The statement below is the
negation of the conjecture.

A set $A$ with a graph on it is given by a finite type `V`, a graph `G` on `V` and an injection
`a : V ↪ ℕ` (so $A$ is the image of `a` and $n$ is `Fintype.card V`). Here `ℕ` contains $0$; see
`erdos_808.variants.positive` for positive integers.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos808.lean#L1746"]
theorem erdos_808 :
    ¬ ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (a : V ↪ ℕ) (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (Fintype.card V : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
        (Fintype.card V : ℝ) ^ (1 + c - ε) ≤
          max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ) := by
  sorry

/--
The conjecture already fails for positive integers: the set of integers constructed in
[ARS20, Theorem 3] consists of positive integers. This is `erdos_808` with the extra hypothesis
`∀ v, 0 < a v`, so it implies `erdos_808`.
-/
@[category research solved, AMS 5 11]
theorem erdos_808.variants.positive :
    ¬ ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (a : V ↪ ℕ), (∀ v, 0 < a v) →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          n₀ ≤ Fintype.card V →
          (Fintype.card V : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
          (Fintype.card V : ℝ) ^ (1 + c - ε) ≤
            max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Alon, Ruzsa, and Solymosi do prove, however, that if $A$ has size $n$ and $G$ has $m$ edges then
$$\max(\lvert A+_GA\rvert,\lvert A\cdot_G A\rvert) \gg m^{3/2}n^{-7/4}.$$

This is [ARS20, Theorem 10]. It holds for any $n$-element set of real numbers, and [ARS20]
state it for $\lvert A+_GA\rvert+\lvert A\cdot_GA\rvert$, which is within a factor $2$ of the
maximum. It is written in multiplied-out form, so that $n=0$ needs no division.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos808.lean#L833"]
theorem erdos_808.variants.ars_lower_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj],
        (G.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2) ≤
          K * (Fintype.card V : ℝ) ^ ((7 : ℝ) / 4) *
            max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ) := by
  sorry

end Erdos808
