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
# Erdős Problem 235

*Reference:* [erdosproblems.com/235](https://www.erdosproblems.com/235)

Let $N_k = p_1 \cdots p_k$ be the $k$-th primorial and let $a_1 < \cdots < a_{\varphi(N_k)}$
be the integers less than $N_k$ coprime to $N_k$. Erdős conjectured that the fraction of
consecutive gaps $a_{i+1} - a_i \le c \cdot N_k / \varphi(N_k)$ tends to a limit that is a
continuous function of $c$. This was proved by Hooley.

[Er55c] Erdős, P., _Some problems on number theory_ (1955).

[Ho65] Hooley, C., _On the difference of consecutive numbers prime to n_, Acta Arith. 8 (1963),
343-347.
-/

open Filter Nat Classical

open scoped BigOperators

namespace Erdos235

/-- The $k$-th primorial: product of the first $k$ primes ($p_1 \cdot p_2 \cdots p_k$). -/
noncomputable def primorial (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, nth Nat.Prime i

/-- The sorted list of natural numbers less than $n$ that are coprime to $n$. -/
def sortedCoprimes (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun a => Nat.Coprime a n)).sort (· ≤ ·)

/-- Count consecutive gaps $\le$ threshold in a sorted list of naturals. -/
noncomputable def countSmallGaps : List ℕ → ℝ → ℕ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, threshold =>
    (if ((b : ℝ) - (a : ℝ)) ≤ threshold then 1 else 0) + countSmallGaps (b :: rest) threshold

/-- The fraction of consecutive gaps among reduced residues $\bmod N_k$
that are at most $c \cdot N_k / \varphi(N_k)$. -/
noncomputable def gapFraction (k : ℕ) (c : ℝ) : ℝ :=
  let Nk := primorial k
  let residues := sortedCoprimes Nk
  let threshold := c * (Nk : ℝ) / (Nat.totient Nk : ℝ)
  (countSmallGaps residues threshold : ℝ) / (Nat.totient Nk : ℝ)

/--
Erdős Problem 235 [Er55c] (proved by Hooley [Ho65]):

Let $N_k = 2 \cdot 3 \cdots p_k$ (the $k$-th primorial) and let
$a_1 < a_2 < \cdots < a_{\varphi(N_k)}$ be the integers less than $N_k$ coprime to $N_k$.
Then for any $c \ge 0$, the limit
$$
\lim_{k \to \infty} \frac{\#\{i : a_i - a_{i-1} \le c \cdot N_k / \varphi(N_k)\}}{\varphi(N_k)}
$$
exists and defines a continuous function of $c$.

Hooley proved that the limiting distribution is exponential: $f(c) = 1 - e^{-c}$.
-/
@[category research solved, AMS 11]
theorem erdos_235 :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ c : ℝ, 0 ≤ c →
        Tendsto (fun k => gapFraction k c) atTop (nhds (f c)) := by
  sorry

end Erdos235
