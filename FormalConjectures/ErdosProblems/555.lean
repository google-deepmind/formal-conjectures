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

import FormalConjecturesUtil

/-!
# Erdős Problem 555

*Reference:* [erdosproblems.com/555](https://www.erdosproblems.com/555)
-/

namespace Erdos555

/-- A symmetric edge-colouring of the complete graph on $m$ vertices with $k$ colours. -/
structure EdgeColoring (m k : ℕ) where
  color : Fin m → Fin m → Fin k
  symm : ∀ u v : Fin m, color u v = color v u

/-- The adjacency relation of the cycle $C_{2n}$ on vertices $0,\ldots,2n-1$. -/
def EvenCycleAdj (n : ℕ) (u v : Fin (2 * n)) : Prop :=
  (u.val + 1) % (2 * n) = v.val ∨ (v.val + 1) % (2 * n) = u.val

/-- A monochromatic copy of a graph with adjacency predicate `Adj`. -/
def ContainsMonochromaticCopy {v m k : ℕ}
    (Adj : Fin v → Fin v → Prop) (χ : EdgeColoring m k) : Prop :=
  ∃ emb : Fin v → Fin m,
    Function.Injective emb ∧
      ∃ c : Fin k,
        ∀ a b : Fin v, Adj a b → χ.color (emb a) (emb b) = c

/-- The natural number $r$ is the Ramsey number $R_k(C_{2n})$, where $n\geq 2$. -/
def IsEvenCycleRamseyNumber (k n r : ℕ) : Prop :=
  2 ≤ n ∧
    IsLeast
      {m : ℕ |
        ∀ χ : EdgeColoring m k, ContainsMonochromaticCopy (EvenCycleAdj n) χ}
      r

/-- A function giving $R_k(C_{2n})$ for every $k\geq 1$ and $n\geq 2$. -/
def EvenCycleRamseyFunction (R : ℕ → ℕ → ℕ) : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 2 ≤ n → IsEvenCycleRamseyNumber k n (R k n)

/--
Let $R_k(G)$ be the least $m$ such that every $k$-colouring of the edges of $K_m$ contains a
monochromatic copy of $G$. Determine $R_k(C_{2n})$.
-/
@[category research open, AMS 5]
theorem erdos_555 : EvenCycleRamseyFunction answer(sorry) := by
  sorry

end Erdos555
