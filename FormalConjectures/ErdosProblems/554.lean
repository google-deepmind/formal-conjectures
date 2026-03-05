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
# Erdős Problem 554

*Reference:* [erdosproblems.com/554](https://www.erdosproblems.com/554)

A problem of Erdős and Graham [Er81c]. The problem is open even for $n = 2$.

[Er81c] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathématique, 1981.
-/

open SimpleGraph

namespace Erdos554

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- The $k$-colour Ramsey number $R_k(G)$: the minimum $N$ such that for every
$k$-colouring of the edges of $K_N$, there is a monochromatic copy of $G$.

A $k$-colouring is a symmetric function $c : \operatorname{Fin} N \to \operatorname{Fin} N \to
\operatorname{Fin} k$. A monochromatic copy of $G$ in colour $a$ is an injective map
$f : V \to \operatorname{Fin} N$ such that every edge of $G$ maps to an edge of colour $a$. -/
noncomputable def multicolorRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a : Fin k) (f : V → Fin N), Function.Injective f ∧
      ∀ u v, G.Adj u v → c (f u) (f v) = a}

/--
Erdős Problem 554 [Er81c]:

For any $n \geq 2$,
$$\lim_{k \to \infty} R_k(C_{2n+1}) / R_k(K_3) = 0.$$

Formulated as: for every $\varepsilon > 0$, there exists $K_0$ such that for all $k \geq K_0$,
$R_k(C_{2n+1}) \leq \varepsilon \cdot R_k(K_3)$.
-/
@[category research open, AMS 5]
theorem erdos_554 (n : ℕ) (hn : n ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n + 1) (by omega)) k : ℝ) ≤
        ε * (multicolorRamseyNumber (⊤ : SimpleGraph (Fin 3)) k : ℝ) := by
  sorry

end Erdos554
