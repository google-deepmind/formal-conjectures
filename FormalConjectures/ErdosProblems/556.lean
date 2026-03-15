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
# Erdős Problem 556

*Reference:* [erdosproblems.com/556](https://www.erdosproblems.com/556)

A problem of Bondy and Erdős. This inequality is best possible for odd $n$.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica **1** (1981), 25–42.

[Er81c] Erdős, P., _Some new problems and results in graph theory and other branches of
  combinatorial mathematics_. Combinatorics and graph theory (1981), 9–17.

[Lu99] Łuczak, T., _R(Cₙ,Cₙ,Cₙ)≤(4+o(1))n_. Journal of Combinatorial Theory Series B
  (1999), 174–187.

[KSS05] Kohayakawa, Y., Simonovits, M., Skokan, J., _The 3-colored Ramsey number of odd
  cycles_. Proceedings of GRACO2005 (2005), 397–402.

[BeSk09] Benevides, F.S., Skokan, J., _The 3-colored Ramsey number of even cycles_. Journal
  of Combinatorial Theory Series B (2009), 690–708.

See also OEIS [A389335](https://oeis.org/A389335).
-/

open SimpleGraph

namespace Erdos556

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- The $k$-colour Ramsey number $R_k(G)$: the minimum $N$ such that for every
$k$-colouring of the edges of $K_N$, there is a monochromatic copy of $G$.

A $k$-colouring is a symmetric function $c : \operatorname{Fin} N \to \operatorname{Fin} N \to \operatorname{Fin} k$.
A monochromatic copy of $G$ in colour $a$ is an injective map $f : V \to \operatorname{Fin} N$
such that every edge of $G$ maps to an edge of colour $a$. -/
noncomputable def multicolorRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a : Fin k) (f : V → Fin N), Function.Injective f ∧
      ∀ u v, G.Adj u v → c (f u) (f v) = a}

/--
Erdős Problem 556 [Er81][Er81c]:

For all $n \geq 3$, the 3-colour Ramsey number of the cycle $C_n$ satisfies
$$R_3(C_n) \leq 4n - 3.$$
-/
@[category research solved, AMS 5]
theorem erdos_556 (n : ℕ) (hn : n ≥ 3) :
    multicolorRamseyNumber (cycleGraph n hn) 3 ≤ 4 * n - 3 := by
  sorry

end Erdos556
