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
module

public import FormalConjecturesUtil

/-!
# McCarthy–Osburn–Straub Conjecture 1.3 for $\sigma_8$, with a shifted companion

For $n \ge 0$ let
$$A(n) = \sum_{\substack{k \in [0, n]^4 \\ k_1 + k_2 = k_3 + k_4}}
  \prod_{i=1}^{4} \binom{n}{k_i} \binom{n + k_i}{k_i},$$
so $A(0), A(1), A(2), A(3) = 1, 33, 8929, 4124193$.

McCarthy, Osburn and Straub [MOS20, Proposition 3.1] show that $A(n)$ is the leading coefficient
$A_{\sigma_8}(n)$ of Brown's cellular integral for $\sigma_8 = (8, 3, 6, 1, 4, 7, 2, 5)$. Their
proof of that proposition is computer-assisted. Their Conjecture 1.3 says, for this $\sigma_8$,
that $A(m p^r) \equiv A(m p^{r-1}) \pmod{p^{3r}}$ for every prime $p \ge 5$ and all $m, r \ge 1$.

* `tower` states this congruence for the explicit sum $A(n)$. Through [MOS20, Proposition 3.1]
  it is Conjecture 1.3 for $\sigma_8$. The Lean statement does not formalize that link.
* `shifted_tower` states the companion $A(m p^r - 1) \equiv A(m p^{r-1} - 1) \pmod{p^{3r}}$, which
  no source states.

*References:*
- [MOS20] D. McCarthy, R. Osburn and A. Straub, *Sequences, modular forms and cellular
  integrals*, Math. Proc. Cambridge Philos. Soc. (2020); arXiv:1705.05586. Proposition 3.1 and
  Conjecture 1.3.
-/

@[expose] public section

open Finset

namespace Arxiv.«1705.05586»

/-- The summand $\binom{n}{k} \binom{n + k}{k}$. -/
def term (n k : ℕ) : ℕ := n.choose k * (n + k).choose k

/-- The MOS sum $A(n)$: the sum over $k \in [0, n]^4$ with $k_1 + k_2 = k_3 + k_4$ of
$\prod_{i=1}^{4} \binom{n}{k_i} \binom{n + k_i}{k_i}$. -/
def A (n : ℕ) : ℕ :=
  ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1),
    if k₁ + k₂ = k₃ + k₄ then term n k₁ * term n k₂ * term n k₃ * term n k₄ else 0

/-- MOS Conjecture 1.3 for $\sigma_8$, for the sum $A(n)$: for every prime $p \ge 5$ and all
$m, r \ge 1$, $A(m p^r) \equiv A(m p^{r-1}) \pmod{p^{3r}}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000001"]
theorem tower (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    A (m * p ^ r) ≡ A (m * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

/-- The shifted companion: for every prime $p \ge 5$ and all $m, r \ge 1$,
$A(m p^r - 1) \equiv A(m p^{r-1} - 1) \pmod{p^{3r}}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000001"]
theorem shifted_tower (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m)
    (hr : 1 ≤ r) :
    A (m * p ^ r - 1) ≡ A (m * p ^ (r - 1) - 1) [MOD p ^ (3 * r)] := by
  sorry

end Arxiv.«1705.05586»

end
