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
# Erdős Problem 558

*Reference:* [erdosproblems.com/558](https://www.erdosproblems.com/558)

Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured
then there is a monochromatic copy of $G$. Determine $R_k(K_{s,t})$
where $K_{s,t}$ is the complete bipartite graph with $s$ vertices in one part
and $t$ in the other.

[ChGr75] Chung, F.R.K. and Graham, R.L., *On multicolor Ramsey numbers for complete
bipartite graphs*, J. Combin. Theory Ser. B 18 (1975), 164–169.

[ARS99] Alon, N., Rónyai, L. and Szabó, T., *Norm-graphs: variations and applications*,
J. Combin. Theory Ser. B 76 (1999), 280–290.
-/

namespace Erdos558

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
Erdős Problem 558: Determine $R_k(K_{s,t})$, the $k$-colour Ramsey number of the
complete bipartite graph $K_{s,t}$. The general problem remains open.
-/
@[category research open, AMS 5]
theorem erdos_558 :
    ∀ s t : ℕ, s ≥ 1 → t ≥ 1 → ∀ k : ℕ,
    multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k = answer((sorry : ℕ → ℕ → ℕ → ℕ) s t k) := by
  sorry

/--
Erdős Problem 558, Chung–Graham result [ChGr75]:

$R_k(K_{2,2}) = (1+o(1))k^2$, i.e., for every $\varepsilon > 0$, there exists $K_0$
such that for all $k \geq K_0$,
$$
(1 - \varepsilon)k^2 \leq R_k(K_{2,2}) \leq (1 + \varepsilon)k^2.
$$
-/
@[category research solved, AMS 5]
theorem erdos_558.variants.K22 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (1 - ε) * (k : ℝ) ^ 2 ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin 2) (Fin 2)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin 2) (Fin 2)) k : ℝ) ≤
        (1 + ε) * (k : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 558, Alon–Rónyai–Szabó result [ARS99]:

$R_k(K_{3,3}) = (1+o(1))k^3$, i.e., for every $\varepsilon > 0$, there exists $K_0$
such that for all $k \geq K_0$,
$$
(1 - \varepsilon)k^3 \leq R_k(K_{3,3}) \leq (1 + \varepsilon)k^3.
$$
-/
@[category research solved, AMS 5]
theorem erdos_558.variants.K33 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (1 - ε) * (k : ℝ) ^ 3 ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin 3) (Fin 3)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin 3) (Fin 3)) k : ℝ) ≤
        (1 + ε) * (k : ℝ) ^ 3 := by
  sorry

/--
Erdős Problem 558, Alon–Rónyai–Szabó result [ARS99]:

If $s \geq (t-1)! + 1$ then $R_k(K_{s,t}) \asymp k^t$, i.e., there exist constants
$C_1, C_2 > 0$ such that for all sufficiently large $k$,
$$
C_1 \cdot k^t \leq R_k(K_{s,t}) \leq C_2 \cdot k^t.
$$
-/
@[category research solved, AMS 5]
theorem erdos_558.variants.ars (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1)
    (hst : s ≥ Nat.factorial (t - 1) + 1) :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      C₁ * (k : ℝ) ^ t ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ≤
        C₂ * (k : ℝ) ^ t := by
  sorry

/--
Erdős Problem 558, Chung–Graham explicit bounds [ChGr75]:

For all $s \geq 1$, $t \geq 2$, and $k \geq 1$,
$$
(2\pi\sqrt{st})^{1/(s+t)} \cdot \frac{s+t}{e^2} \cdot k^{(st-1)/(s+t)}
\leq R_k(K_{s,t})
\leq (t-1)(k + k^{1/s})^s.
$$
-/
@[category research solved, AMS 5]
theorem erdos_558.variants.chung_graham (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 2) :
    ∀ k : ℕ, k ≥ 1 →
      (2 * Real.pi * Real.sqrt ((s : ℝ) * t)) ^ ((1 : ℝ) / ((s : ℝ) + t)) *
        (((s : ℝ) + t) / (Real.exp 1) ^ 2) *
        (k : ℝ) ^ (((s : ℝ) * t - 1) / ((s : ℝ) + t)) ≤
          (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ≤
        ((t : ℝ) - 1) * ((k : ℝ) + (k : ℝ) ^ ((1 : ℝ) / (s : ℝ))) ^ (s : ℕ) := by
  sorry

end Erdos558
