/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 192

*References:*
- [erdosproblems.com/192](https://www.erdosproblems.com/192)
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ke92] Keränen, Veikko, *Abelian squares are avoidable on $4$ letters*. Automata, languages and
  programming (Vienna, 1992) (1992), 41-52.
- [FiPu23] Fici, Gabriele and Puzynina, Svetlana, *Abelian combinatorics on words: a survey*.
  Comput. Sci. Rev. (2023), Paper No. 100532, 21.
-/

@[expose] public section

namespace Erdos192

/-- A sequence $a_1, a_2, \ldots \in \mathbb{R}^d$ such that every difference $a_{i+1}-a_i$ is a
positive unit vector $(0,\ldots,0,1,0,\ldots,0)$. -/
def IsPositiveUnitWalk {d : ℕ} (a : ℕ → Fin d → ℝ) : Prop :=
  ∀ n, ∃ i : Fin d, ∀ j, a (n + 1) j = a n j + if j = i then 1 else 0

/--
Let $A=\{a_1,a_2,\ldots\}\subset \mathbb{R}^d$ be an infinite sequence such that $a_{i+1}-a_i$
is a positive unit vector (i.e. is of the form $(0,0,\ldots,1,0,\ldots,0)$). For which $d$ must
$A$ contain a three-term arithmetic progression?

This is true for $d\leq 3$ and false for $d\geq 4$.

This problem is equivalent to one on 'abelian squares' (see
[231](https://www.erdosproblems.com/231)). In particular $A$ can be interpreted as an infinite
string over an alphabet with $d$ letters (each letter describining which of the $d$ possible
steps is taken at each point). An abelian square in a string $s$ is a pair of consecutive blocks
$x$ and $y$ appearing in $s$ such that $y$ is a permutation of $x$. The connection comes from the
observation that $p,q,r\in A\subset \mathbb{R}^d$ form a three-term arithmetic progression if and
only if the string corresponding to the steps from $p$ to $q$ is a permutation of the string
corresponding to the steps from $q$ to $r$.

This problem is therefore equivalent to asking for which $d$ there exists an infinite string over
$\{1,\ldots,d\}$ with no abelian squares. An infinite string without abelian squares was
constructed when $d=4$ by Keränen [Ke92]. We refer to a recent survey by Fici and Puzynina
[FiPu23] for more background and related results.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos192.lean#L39"]
theorem erdos_192 : {d : ℕ | ∀ a : ℕ → Fin d → ℝ, IsPositiveUnitWalk a →
    ∃ x ∈ Set.range a, ∃ y ∈ Set.range a, ∃ z ∈ Set.range a, x ≠ y ∧ ∀ j, x j + z j = 2 * y j} =
      answer(Set.Iic 3) := by
  sorry

end Erdos192
