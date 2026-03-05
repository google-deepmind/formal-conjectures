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
# Erdős Problem 555

*Reference:* [erdosproblems.com/555](https://www.erdosproblems.com/555)

Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured
then there is a monochromatic copy of $G$. Determine the value of $R_k(C_{2n})$.

A problem of Erdős and Graham. Erdős [Er81c] gives the bounds
$$k^{1 + 1/(2n)} \ll R_k(C_{2n}) \ll k^{1 + 1/(n-1)}.$$

Chung and Graham [ChGr75] showed that
$R_k(C_4) > k^2 - k + 1$ when $k-1$ is a prime power, and
$R_k(C_4) \leq k^2 + k + 1$ for all $k$.
-/

open SimpleGraph

namespace Erdos555

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
Erdős Problem 555, lower bound [Er81c]:

For every $n \geq 2$, there exist $C > 0$ and $K_0$ such that for all $k \geq K_0$,
$$R_k(C_{2n}) \geq C \cdot k^{1 + 1/(2n)}.$$
-/
@[category research solved, AMS 5]
theorem erdos_555 (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n) (by omega)) k : ℝ) ≥
        C * (k : ℝ) ^ ((1 : ℝ) + 1 / (2 * (n : ℝ))) := by
  sorry

/--
Erdős Problem 555, upper bound [Er81c]:

For every $n \geq 2$, there exist $C > 0$ and $K_0$ such that for all $k \geq K_0$,
$$R_k(C_{2n}) \leq C \cdot k^{1 + 1/(n - 1)}.$$
-/
@[category research solved, AMS 5]
theorem erdos_555.variants.upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n) (by omega)) k : ℝ) ≤
        C * (k : ℝ) ^ ((1 : ℝ) + 1 / ((n : ℝ) - 1)) := by
  sorry

/--
Chung–Graham upper bound [ChGr75]: $R_k(C_4) \leq k^2 + k + 1$ for all $k \geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_555.variants.chung_graham_upper (k : ℕ) (hk : k ≥ 2) :
    multicolorRamseyNumber (cycleGraph 4 (by omega)) k ≤ k ^ 2 + k + 1 := by
  sorry

end Erdos555
