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
# Erdős Problem 78

*Reference:* [erdosproblems.com/78](https://www.erdosproblems.com/78)

Give a constructive proof that $R(k) > C^k$ for some constant $C > 1$, where $R(k)$ is the
diagonal Ramsey number. Erdős's probabilistic proof that $R(k) \gg k \cdot 2^{k/2}$ is
non-constructive. Prize: \$100.
-/

open SimpleGraph

namespace Erdos78

/--
Erdős Problem 78 (Open, \$100 prize):

Let $R(k)$ be the Ramsey number for $K_k$, the minimal $n$ such that every
2-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$.
Give a constructive proof that $R(k) > C^k$ for some constant $C > 1$.

Erdős gave a simple probabilistic (non-constructive) proof that
$R(k) \gg k \cdot 2^{k/2}$. This problem asks for an explicit/constructive
lower bound that is still exponential in $k$.

Equivalently, this asks for an explicit construction of a graph on $n$
vertices which does not contain any clique or independent set of size
$\geq c \cdot \log(n)$ for some constant $c > 0$.

We formalize the core mathematical content: there exists $C > 1$ such that
for all $k \geq 2$, there exists a graph on at least $C^k$ vertices with no
clique or independent set of size $k$ (an independent set of size $k$ in $G$
is a clique of size $k$ in $G^c$). The "constructive" requirement pertains
to the nature of the proof, not the formal statement itself.
-/
@[category research open, AMS 5]
theorem erdos_78 :
    ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, (C ^ k : ℝ) ≤ ↑n ∧
        ∃ G : SimpleGraph (Fin n),
          G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  sorry

end Erdos78
