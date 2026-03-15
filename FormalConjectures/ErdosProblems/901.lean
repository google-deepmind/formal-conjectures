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
# Erdős Problem 901

Let $m(n)$ denote the minimum number of edges in an $n$-uniform hypergraph that does not have
Property B (i.e., is not $2$-colorable). Erdős and Lovász conjectured that $m(n)$ is of order
$n \cdot 2^n$.

*Reference:* [erdosproblems.com/901](https://www.erdosproblems.com/901)

[ErLo75] Erdős, P. and Lovász, L., _Problems and results on 3-chromatic hypergraphs and some
related questions_. Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on
his 60th birthday), Vol. II (1975), 609–627.

[Er64e] Erdős, P., _On a combinatorial problem. II_. Acta Mathematica Academiae Scientiarum
Hungaricae **15** (1964), 445–447.
-/

open Finset

namespace Erdos901

/--
An $n$-uniform hypergraph is a finite collection of edges where each edge
has exactly $n$ vertices.
-/
def IsNUniform (H : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ e ∈ H, e.card = n

/--
A hypergraph has Property B (is $2$-colorable) if there exists a $2$-coloring
of the vertex set such that no edge is monochromatic, i.e., every edge
contains vertices of both colors.
-/
def HasPropertyB (H : Finset (Finset ℕ)) : Prop :=
  ∃ f : ℕ → Bool, ∀ e ∈ H, (∃ x ∈ e, f x = true) ∧ (∃ x ∈ e, f x = false)

/--
Erdős Problem 901 (Erdős–Lovász Conjecture), lower bound:
Let $m(n)$ be minimal such that there is an $n$-uniform hypergraph with $m(n)$ edges
that does not have Property B. Erdős and Lovász conjecture that $m(n)$ is of
order $n \cdot 2^n$.

Lower bound: there exists $c > 0$ such that for all sufficiently large $n$,
every $n$-uniform hypergraph without Property B has at least $c \cdot n \cdot 2^n$ edges.
-/
@[category research open, AMS 5]
theorem erdos_901 :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (H : Finset (Finset ℕ)),
        IsNUniform H n → ¬HasPropertyB H →
        (H.card : ℝ) ≥ c * ↑n * (2 : ℝ) ^ n := by
  sorry

/--
Erdős Problem 901 (Erdős–Lovász Conjecture), upper bound:
There exists $c > 0$ such that for all sufficiently large $n$, there exists
an $n$-uniform hypergraph without Property B with at most $c \cdot n \cdot 2^n$ edges.
-/
@[category research open, AMS 5]
theorem erdos_901.variants.upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ (H : Finset (Finset ℕ)),
        IsNUniform H n ∧ ¬HasPropertyB H ∧
        (H.card : ℝ) ≤ c * ↑n * (2 : ℝ) ^ n := by
  sorry

end Erdos901
