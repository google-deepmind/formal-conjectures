/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 985

*References:*
- [erdosproblems.com/985](https://www.erdosproblems.com/985)
- [MTT16] McGown, K., Treviño, E. and Trudgian, T., *Resolving Grosswald's conjecture on GRH*.
  Funct. Approx. Comment. Math. 55 (2016), 215–225.
  [arXiv:1508.05182](https://arxiv.org/abs/1508.05182)
- [Al26] Alpöge, L., [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf) (2026).
-/

@[expose] public section

namespace Erdos985

/--
Is it true that, for every prime $p$, there is a prime $q \leq p$ which is a primitive root modulo $p$?

The answer is yes. Assuming the Generalized Riemann Hypothesis for Dirichlet $L$-functions, the
least prime primitive root modulo $p$ is less than $\sqrt{p} - 2$ for every prime $p > 2791$
[MTT16, Theorem 1]. A finite computation covers the odd primes $p \leq 2791$. The Generalized
Riemann Hypothesis is proved [Al26].
-/
@[category research solved, question, AMS 11]
theorem erdos_985 : ∀ᵉ (p : ℕ) (hp_prime : p.Prime) (hp_nontrivial : p ≠ 2),
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  sorry

/--
The quantitative form of the argument above: for every prime $p > 2791$ there is a prime
$q < \sqrt{p} - 2$ which is a primitive root modulo $p$. McGown, Treviño and Trudgian proved this
assuming the Generalized Riemann Hypothesis for Dirichlet $L$-functions [MTT16, Theorem 1], which
enters only through Bach's explicit bounds for $\sum \Lambda(n)\chi(n)$ over characters modulo $p$.
That hypothesis is now proved [Al26]. The bound $2791$ is sharp: $p = 2791$ has no prime primitive
root below $\sqrt{2791} - 2$.
-/
@[category research solved, AMS 11]
theorem erdos_985.variants.sqrt_bound (p : ℕ) (hp : p.Prime) (hp' : 2791 < p) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) < √p - 2 ∧ orderOf (q : ZMod p) = p - 1 := by
  sorry

-- TODO: Artin conjectured that 2 is a primitive root for infinitely many primes $p$, which
-- Hooley proved assuming the Riemann hypothesis for the Dedekind zeta functions of certain Kummer
-- fields.

/--
Heath-Brown proved that at least one of 2, 3, or 5 is a primitive root for infinitely many primes $p$.
-/
@[category research solved, AMS 11]
theorem erdos_985.variants.two_three_five_primitive_root :
    Set.Infinite
      {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨
       orderOf (3 : ZMod p) = p - 1 ∨
       orderOf (5 : ZMod p) = p - 1)} := by
  sorry

end Erdos985
