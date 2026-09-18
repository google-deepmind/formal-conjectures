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
# Erdős Problem 1025

*References:*
- [erdosproblems.com/1025](https://www.erdosproblems.com/1025)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [ErHa58] Erdős, P. and Hajnal, A., *On the structure of set mappings*. Acta Math. Acad. Sci.
  Hungar. (1958), 111-133.
- [Sp72] Spencer, Joel, *Turán's theorem for $k$-graphs*. Discrete Math. (1972), 183--186.
- [CFS16] Conlon, David and Fox, Jacob and Sudakov, Benny, *Short proofs of some extremal results
  II*. J. Combin. Theory Ser. B (2016), 173--196.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1025

/-- `X` is independent for a set mapping `f` on pairs if `f s(x, y) ∉ X` whenever `x ≠ y` are in
`X`. -/
def IsIndependent {n : ℕ} (f : Sym2 (Fin n) → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f s(x, y) ∉ X

/-- `g n` is the largest `k` such that every set mapping `f` on the pairs of an `n`-element set
with `f(x, y) ∉ {x, y}` admits an independent set of size at least `k`. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | k ≤ n ∧ ∀ f : Sym2 (Fin n) → Fin n,
    (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
      ∃ X : Finset (Fin n), IsIndependent f X ∧ k ≤ X.card}

/--
Let $f$ be a function from all pairs of elements in $\{1,\ldots,n\}$ to $\{1,\ldots,n\}$ such
that $f(x,y)\neq x$ and $\neq y$ for all $x,y$. We call $X\subseteq \{1,\ldots,n\}$ independent
if whenever $x,y\in X$ we have $f(x,y)\not\in X$.

Let $g(n)$ be such that, in every function $f$, there is an independent set of size at least
$g(n)$. Estimate $g(n)$.

A question of Erdős and Hajnal [ErHa58], who could prove $n^{1/3} \ll g(n) \ll (n\log n)^{1/2}$.
Spencer [Sp72] proved $g(n)\gg n^{1/2}$. Conlon, Fox, and Sudakov [CFS16] proved
$g(n)\ll n^{1/2}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1025.lean#L829"]
theorem erdos_1025 : (fun n : ℕ => (g n : ℝ)) =Θ[atTop] fun n : ℕ => √n := by
  sorry

end Erdos1025
