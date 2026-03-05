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
# Erdős Problem 280

*Reference:* [erdosproblems.com/280](https://www.erdosproblems.com/280)

Let $n_1 < n_2 < \cdots$ be an infinite sequence of integers with associated residue
classes $a_k \pmod{n_k}$, such that for some $\varepsilon > 0$ we have
$n_k > (1+\varepsilon)k \log k$ for all $k \geq 1$. Erdős and Graham conjectured that
$$\#\{m < n_k : m \not\equiv a_i \pmod{n_i} \text{ for } 1 \leq i \leq k\} \neq o(k).$$

This was disproved by Cambie, who observed that taking $n_k = 2^k$ and
$a_k = 2^{k-1} + 1$ for $k \geq 1$ gives a trivial counterexample: the only $m$
not in any congruence class is $1$, so the count is $1$ for all $k$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos280

open Classical in
/-- The count of integers $m < n(k)$ that avoid all congruence classes $a(i) \bmod n(i)$
for $1 \leq i \leq k$. -/
noncomputable def sieveCount (n a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range (n k)).filter fun m =>
    ∀ i ∈ Finset.Icc 1 k, ¬(m ≡ a i [MOD n i])).card

/--
Erdős Problem 280 (Disproved) [ErGr80, p.29]:

There exist a strictly increasing sequence $n_1 < n_2 < \cdots$ of positive integers
and associated residue classes $a_k \pmod{n_k}$, with $n_k > (1+\varepsilon)k \log k$
for some $\varepsilon > 0$ and all $k \geq 1$, such that the sieve count
$$\#\{m < n_k : m \not\equiv a_i \pmod{n_i} \text{ for } 1 \leq i \leq k\}$$
is $o(k)$ as $k \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_280 :
    ∃ (n : ℕ → ℕ) (a : ℕ → ℕ) (ε : ℝ),
      0 < ε ∧
      StrictMono n ∧
      (∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * ↑k * Real.log ↑k) ∧
      ∀ c : ℝ, 0 < c →
        ∃ K : ℕ, ∀ k, K ≤ k →
          (sieveCount n a k : ℝ) < c * ↑k := by
  sorry

end Erdos280
