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
# Erdős Problem 682

*References:*
- [erdosproblems.com/682](https://www.erdosproblems.com/682)
- [Er79d] Erdős, P., Some unconventional problems in number theory. Acta Math. Acad. Sci. Hungar.
  (1979), 71-80.
- [GaTa25] A. Gafni and T. Tao, Rough numbers between consecutive primes. arXiv:2508.06463 (2025).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos682

/-- The `n`th prime, indexed from zero: `p 0 = 2`, `p 1 = 3`, ... -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
Is it true that for almost all $n$ there exists some $m\in (p_n,p_{n+1})$ such that
$$p(m) \geq p_{n+1}-p_n,$$
where $p(m)$ denotes the least prime factor of $m$?

This was solved in the affirmative by Gafni and Tao [GaTa25].

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos682.lean#L5018"]
theorem erdos_682 : answer(True) ↔
    {n | ∃ m ∈ Set.Ioo (p n) (p (n + 1)), p (n + 1) - p n ≤ m.minFac}.HasDensity 1 := by
  sorry

open scoped Classical in
/--
Gafni and Tao [GaTa25] proved that the number of exceptional $n\in [1,X]$ is
$$\ll \frac{X}{(\log X)^2}.$$
-/
@[category research solved, AMS 11]
theorem erdos_682.variants.exceptional_count :
    (fun X : ℕ ↦ ({n ∈ Finset.Icc 1 X |
        ∀ m ∈ Set.Ioo (p n) (p (n + 1)), m.minFac < p (n + 1) - p n}.card : ℝ)) =O[atTop]
      fun X : ℕ ↦ (X : ℝ) / Real.log X ^ 2 := by
  sorry

/--
Erdős first thought this should be true for all large $n$, but found a (conditional)
counterexample: Dickson's conjecture says there are infinitely many $d$ such that
$$2183+30030d\textrm{ and }2201+30030d$$
are both prime, and then they must necessarily be consecutive primes. These give a counterexample
since $30030=2\cdot 3 \cdot 5\cdot 7\cdot 11\cdot 13$ and every integer in $[2184,2200]$ is
divisible by at least one of these primes.

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category textbook, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos682.lean#L5222"]
theorem erdos_682.variants.dickson_counterexample (d : ℕ) (h₁ : (2183 + 30030 * d).Prime)
    (h₂ : (2201 + 30030 * d).Prime) : ∃ n, p n = 2183 + 30030 * d ∧ p (n + 1) = 2201 + 30030 * d ∧
      ∀ m ∈ Set.Ioo (p n) (p (n + 1)), m.minFac < p (n + 1) - p n := by
  sorry

end Erdos682
