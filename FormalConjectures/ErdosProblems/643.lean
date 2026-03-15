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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 643

*Reference:* [erdosproblems.com/643](https://www.erdosproblems.com/643)

Let $f(n;t)$ be minimal such that if a $t$-uniform hypergraph on $n$ vertices
contains at least $f(n;t)$ edges then there must be four edges $A,B,C,D$ such
that $A \cup B = C \cup D$ and $A \cap B = C \cap D = \emptyset$.

Estimate $f(n;t)$ — in particular, is it true that for $t \geq 3$,
$f(n;t) = (1+o(1))\binom{n}{t-1}$?

For $t=2$ this asks for the maximum number of edges in a graph with no $C_4$,
giving $f(n;2) = (1/2+o(1))n^{3/2}$.

Füredi [Fu84] proved $f(n;3) \ll n^2$ and $f(n;3) > \binom{n}{2}$ for
infinitely many $n$. Pikhurko and Verstraëte [PiVe09] proved
$f(n;3) \leq \frac{13}{9}\binom{n}{2}$ for all $n$.

More generally, Füredi proved
$\binom{n-1}{t-1} + \lfloor(n-1)/t\rfloor \leq f(n;t) < \frac{7}{2}\binom{n}{t-1}$,
and conjectured the lower bound is sharp for $t \geq 4$.

Pikhurko and Verstraëte proved
$1 \leq \limsup_{n\to\infty} f(n;t)/\binom{n}{t-1} \leq \min(7/4, 1+2/\sqrt{t})$
for all $t \geq 3$.

[Er77b] Erdős, P., _Problems and results in combinatorial analysis_.
Proceedings of the Eighth Southeastern Conference on Combinatorics, Graph Theory
and Computing (1977), 3–12.

[Er97d] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. (1997), 81–85.

[Fu84] Füredi, Z., _Hypergraphs in which all disjoint pairs have distinct unions_.
Combinatorica (1984), 161–168.

[PiVe09] Pikhurko, O. and Verstraëte, J., _The maximum size of hypergraphs without
generalized 4-cycles_. J. Combin. Theory Ser. A (2009), 637–649.
-/

namespace Erdos643

/-- A $t$-uniform hypergraph on `Fin n`: a family of $t$-element subsets. -/
def IsUniformHypergraph (n t : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = t

/-- A hypergraph contains the "complementary pairs" configuration:
    edges $A, B, C, D$ with $A \cup B = C \cup D$, both pairs disjoint,
    and $\{A, B\} \neq \{C, D\}$ as unordered pairs. -/
def HasComplementaryPairs {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ A B C D : Finset (Fin n),
    A ∈ H ∧ B ∈ H ∧ C ∈ H ∧ D ∈ H ∧
    A ∪ B = C ∪ D ∧
    Disjoint A B ∧ Disjoint C D ∧
    ({A, B} : Finset (Finset (Fin n))) ≠ {C, D}

/--
**Erdős Problem 643** [Er77b][Er97d]:

For every $t \geq 3$ and every $\varepsilon > 0$, there exists $N$ such that
for all $n \geq N$, every $t$-uniform hypergraph on $n$ vertices with more than
$(1+\varepsilon)\binom{n}{t-1}$ edges contains the complementary pairs
configuration, and there exists one with at least
$(1-\varepsilon)\binom{n}{t-1}$ edges avoiding it.

Equivalently, $f(n;t) = (1+o(1))\binom{n}{t-1}$ for all $t \geq 3$.
-/
@[category research open, AMS 5]
theorem erdos_643 :
    answer(sorry) ↔
    ∀ t : ℕ, 3 ≤ t →
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ H : Finset (Finset (Fin n)),
        IsUniformHypergraph n t H →
        (H.card : ℝ) > (1 + ε) * (Nat.choose n (t - 1) : ℝ) →
        HasComplementaryPairs H) ∧
      (∃ H : Finset (Finset (Fin n)),
        IsUniformHypergraph n t H ∧
        (H.card : ℝ) ≥ (1 - ε) * (Nat.choose n (t - 1) : ℝ) ∧
        ¬HasComplementaryPairs H) := by
  sorry

end Erdos643
