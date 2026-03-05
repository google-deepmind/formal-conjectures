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
# Erdős Problem 557

*Reference:* [erdosproblems.com/557](https://www.erdosproblems.com/557)

A problem of Erdős and Graham on multicolour Ramsey numbers for trees.

[ErGr75] Erdős, P. and Graham, R., _On partition theorems for finite graphs_.
Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th birthday),
Vol. I; Colloq. Math. Soc. János Bolyai, Vol. 10, North-Holland, Amsterdam, 1975, pp. 515–527.
-/

open SimpleGraph

namespace Erdos557

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
Erdős Problem 557 [ErGr75]:

Is it true that there exists an absolute constant $C$ such that for all $k \ge 1$, all $n \ge 1$,
and all trees $T$ on $n$ vertices, $R_k(T) \le kn + C$?
-/
@[category research open, AMS 5]
theorem erdos_557 : answer(sorry) ↔
    ∃ C : ℕ, ∀ (n : ℕ) (hn : n ≥ 1) (T : SimpleGraph (Fin n)),
      T.IsTree →
      ∀ k : ℕ, k ≥ 1 →
        multicolorRamseyNumber T k ≤ k * n + C := by
  sorry

end Erdos557
