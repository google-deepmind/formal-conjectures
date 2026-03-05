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
# Erdős Problem 1029

*Reference:* [erdosproblems.com/1029](https://www.erdosproblems.com/1029)

If $R(k)$ is the diagonal Ramsey number for $K_k$, the minimal $n$ such that every
2-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$, then
$$
  R(k) / (k \cdot 2^{k/2}) \to \infty.
$$

Erdős and Szekeres [ErSz35] proved $k \cdot 2^{k/2} \ll R(k) \leq \binom{2k-1}{k-1}$.
The probabilistic method gives $R(k) \geq (1+o(1)) \cdot \frac{1}{\sqrt{2}\, e} \cdot k \cdot 2^{k/2}$,
improved by Spencer [Sp75] to $R(k) \geq (1+o(1)) \cdot \frac{\sqrt{2}}{e} \cdot k \cdot 2^{k/2}$.

[ErSz35] Erdős, P. and Szekeres, G., *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463–470.

[Sp75] Spencer, J., *Ramsey's theorem — a new lower bound*, J. Combin. Theory Ser. A 18 (1975), 108–115.

[Er93] Erdős, P., *On some of my favourite theorems* (1993).
-/

open Finset

namespace Erdos1029

/-- The diagonal Ramsey number $R(k)$: the minimum $N$ such that for every
symmetric 2-colouring of the edges of $K_N$, there is a monochromatic
clique of size $k$ in some colour. -/
noncomputable def diagonalRamseyNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (S : Finset (Fin N)), S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b}

/--
Erdős Problem 1029 [Er93, p.337]:

$R(k) / (k \cdot 2^{k/2}) \to \infty$ as $k \to \infty$.

Formulated as: for every $C > 0$, there exists $K_0$ such that for all $k \geq K_0$,
$R(k) \geq C \cdot k \cdot 2^{k/2}$.
-/
@[category research open, AMS 5]
theorem erdos_1029 :
    ∀ C : ℝ, C > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (diagonalRamseyNumber k : ℝ) ≥ C * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
  sorry

end Erdos1029
