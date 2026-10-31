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
# Erdős Problem 805

*References:*
- [erdosproblems.com/805](https://www.erdosproblems.com/805)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [AlSu07] Alon, N. and Sudakov, B., *On graphs with subgraphs having large independence
  numbers*. J. Graph Theory 56 (2007), 149-157.
  [arXiv:0706.4099](https://arxiv.org/abs/0706.4099)
- [ABS21] Alon, N., Bucić, M. and Sudakov, B., *Large cliques and independent sets all over the
  place*. Proc. Amer. Math. Soc. 149 (2021), 3145-3157.
  [arXiv:2004.04718](https://arxiv.org/abs/2004.04718)
-/

@[expose] public section

open Filter

namespace Erdos805

/-- `IsLocallyRamsey G m k`: every set of `m` vertices of `G` contains a clique with at least `k`
vertices and an independent set with at least `k` vertices. -/
def IsLocallyRamsey {n : ℕ} (G : SimpleGraph (Fin n)) (m k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m →
    (∃ C ⊆ S, k ≤ C.card ∧ G.IsClique (C : Set (Fin n))) ∧
    (∃ I ⊆ S, k ≤ I.card ∧ G.IsIndepSet (I : Set (Fin n)))

/-- If every set of `m` vertices contains a clique and an independent set of size `k`, so does
every set of `m' ≥ m` vertices. Thus "every induced subgraph on exactly `m` vertices" and "every
set of at least `m` vertices" (the formulation of [ABS21]) agree. -/
@[category API, AMS 5]
theorem IsLocallyRamsey.mono {n m m' k : ℕ} {G : SimpleGraph (Fin n)}
    (h : IsLocallyRamsey G m k) (hm : m ≤ m') : IsLocallyRamsey G m' k := by
  intro S hS
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show m ≤ S.card by omega)
  obtain ⟨⟨C, hCT, hCk, hC⟩, ⟨I, hIT, hIk, hI⟩⟩ := h T hT
  exact ⟨⟨C, hCT.trans hTS, hCk, hC⟩, ⟨I, hIT.trans hTS, hIk, hI⟩⟩

/-- `HasRamseyGraphs g`: for all sufficiently large `n` there is a graph on `n` vertices in
which every induced subgraph on `g n` vertices contains a clique and an independent set of size
at least $\log n$ (that is, of at least `⌈log n⌉` vertices; `log` is the natural logarithm). -/
def HasRamseyGraphs (g : ℕ → ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G (g n) ⌈Real.log n⌉₊

/-- The answer: the set of functions `g` with $n>g(n)\geq(\log n)^2$ for which such graphs
exist. -/
def erdos_805.parts.i.answer : Set (ℕ → ℕ) := sorry

/--
For which functions $g(n)$ with $n>g(n)\geq (\log n)^2$ is there a graph on $n$ vertices in which
every induced subgraph on $g(n)$ vertices contains a clique of size $\geq \log n$ and an
independent set of size $\geq \log n$?

In particular, is there such a graph for $g(n)=(\log n)^3$?

This is the first part. A problem of Erdős and Hajnal [Er91]; see also
[erdosproblems.com/804](https://www.erdosproblems.com/804). The inequalities
on `g` are required for all large `n`, and a graph is required for all large `n`.
-/
@[category research open, question value, AMS 5]
theorem erdos_805.parts.i :
    {g : ℕ → ℕ | (∀ᶠ n : ℕ in atTop, Real.log n ^ 2 ≤ g n ∧ g n < n) ∧ HasRamseyGraphs g} =
      erdos_805.parts.i.answer := by
  sorry

/--
For which functions $g(n)$ with $n>g(n)\geq (\log n)^2$ is there a graph on $n$ vertices in which
every induced subgraph on $g(n)$ vertices contains a clique of size $\geq \log n$ and an
independent set of size $\geq \log n$?

In particular, is there such a graph for $g(n)=(\log n)^3$?

This is the second part. Erdős and Hajnal thought that there is no such graph for
$g(n)=(\log n)^3$ [AlSu07]; we state the positive proposition, with $g(n)=\lfloor(\log n)^3\rfloor$
and a graph required for all large $n$, as in the first part.
-/
@[category research open, question, AMS 5]
theorem erdos_805.parts.ii : HasRamseyGraphs (fun n ↦ ⌊Real.log n ^ 3⌋₊) := by
  sorry

/--
Alon and Sudakov [AlSu07] proved that there is no such graph with
$$g(n)=\frac{c}{\log\log n}(\log n)^3$$
for some constant $c>0$.

Here `log` is the natural logarithm, as in [AlSu07], and the statement is for all large `n`.
-/
@[category research solved, AMS 5]
theorem erdos_805.variants.alon_sudakov :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ¬ ∃ G : SimpleGraph (Fin n),
      IsLocallyRamsey G ⌊c * Real.log n ^ 3 / Real.log (Real.log n)⌋₊ ⌈Real.log n⌉₊ := by
  sorry

/--
Alon, Bucić, and Sudakov [ABS21] construct such a graph with
$$g(n)\leq 2^{2^{(\log\log n)^{1/2+o(1)}}}.$$

Here all logarithms are to base $2$, as in [ABS21], so the cliques and independent sets have at
least $\lceil\log_2 n\rceil$ vertices; this implies the natural-logarithm version of the problem.
The $o(1)$ is expressed as: for every $0<\varepsilon<1/2$ and all large $n$ there is such a graph
with $g(n)=\lceil 2^{2^{(\log_2\log_2 n)^{1/2+\varepsilon}}}\rceil$. This form, with the rounding,
follows from [ABS21, Theorem 2].
-/
@[category research solved, AMS 5]
theorem erdos_805.variants.alon_bucic_sudakov :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      IsLocallyRamsey G
        ⌈(2 : ℝ) ^ ((2 : ℝ) ^ (Real.logb 2 (Real.logb 2 n) ^ (1 / 2 + ε)))⌉₊
        ⌈Real.logb 2 n⌉₊ := by
  sorry

end Erdos805
