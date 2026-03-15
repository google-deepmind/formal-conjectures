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
# Erdős Problem 336

For $r \geq 2$, let $h(r)$ be the maximal finite $k$ such that there exists an additive basis
$A \subseteq \mathbb{N}$ of order $r$ that also has exact order $k$. Find the value of
$\lim_{r\to\infty} h(r)/r^2$. It is known that $1/3 \leq \lim h(r)/r^2 \leq 1/2$.

*Reference:* [erdosproblems.com/336](https://www.erdosproblems.com/336)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[ErGr80b] Erdős, P. and Graham, R., _On bases with an exact order_. Acta Arithmetica
(1980), 201–207.

[Gr88] Grekos, G., _Sur l'ordre d'une base additive_. (1988), Exp. No. 31, 13 pp.

[Na93] Nash, J.C.M., _Some applications of a theorem of M. Kneser_. Journal of Number
Theory (1993), 1–8.

[Pl04] Plagne, A., _À propos de la fonction X d'Erdős et Graham_. Annales de l'Institut
Fourier (Grenoble) (2004), 1717–1767.
-/

open Filter

open scoped Topology BigOperators

namespace Erdos336

/-- The set of all sums of exactly $k$ elements from $A$ (with repetition allowed). -/
def exactSumset (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $r$ if every sufficiently large
natural number is the sum of at most $r$ elements from $A$. -/
def IsAdditiveBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ k ≤ r, n ∈ exactSumset A k

/-- $A$ has exact order $k$ if every sufficiently large natural number is the sum of
exactly $k$ elements from $A$. -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, n ∈ exactSumset A k

/-- $h(r)$ is the maximal $k$ such that some basis of order $r$ has exact order $k$. -/
noncomputable def hBasis (r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Set ℕ, IsAdditiveBasis A r ∧ HasExactOrder A k}

/--
Erdős Problem 336 [ErGr80, p.51]:

For $r \geq 2$ let $h(r)$ be the maximal finite $k$ such that there exists a basis
$A \subseteq \mathbb{N}$ of order $r$ (every sufficiently large integer is the sum of at most
$r$ elements from $A$) and exact order $k$ (every sufficiently large integer is the sum of
exactly $k$ elements from $A$).

Find the value of $\lim_{r\to\infty} h(r)/r^2$.

Known bounds: $1/3 \leq \lim h(r)/r^2 \leq 1/2$ (lower bound due to Grekos [Gr88], upper
bound due to Nash [Na93]).
-/
@[category research open, AMS 11]
theorem erdos_336 :
    Tendsto (fun r : ℕ => (hBasis r : ℝ) / ((r : ℝ) ^ 2))
      atTop (nhds (answer(sorry))) := by
  sorry

end Erdos336
