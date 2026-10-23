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
# Erdős Problem 1204

*References:*
- [erdosproblems.com/1204](https://www.erdosproblems.com/1204)
- [El65] Elliott, P. D. T. A., *On sequences of integers*. Quart. J. Math. Oxford Ser. (2) 16
  (1965), 35-45.
- [Er80] Erdős, P., *A survey of problems in combinatorial number theory*. Ann. Discrete Math. 6
  (1980), 89-115.
- [Po14c] Polymath, D. H. J., *Variants of the Selberg sieve, and bounded intervals containing
  many primes*. Res. Math. Sci. 1 (2014), Art. 12.
  [arXiv:1407.4897](https://arxiv.org/abs/1407.4897)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1204

/-- A finite set `S` of natural numbers is *admissible* if it misses at least one residue class
modulo every prime. A sequence $0\leq a_1<\cdots <a_k$ is identified with the set of its values. -/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r

/-- $A(k)$: the least possible value of $a_k$ over admissible sequences $0\leq a_1<\cdots <a_k$.
Any $k$ primes larger than $k$ form an admissible set, so `sInf` is a true minimum. -/
noncomputable def A (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∀ a ∈ S, a ≤ m}

/-- The least possible value of $a_1+\cdots+a_k$ over admissible sequences
$0\leq a_1<\cdots <a_k$. As for `A`, the minimum exists. -/
noncomputable def minSum (k : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∑ a ∈ S, a = s}

/-- $B(k)=\min \frac{a_1+\cdots+a_k}{k}$. -/
noncomputable def B (k : ℕ) : ℝ := (minSum k : ℝ) / k

/-- An admissible set of `k` natural numbers inside `[0, m]` gives `A k ≤ m`. -/
@[category API, AMS 11]
theorem A_le {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S)
    (hm : ∀ a ∈ S, a ≤ m) : A k ≤ m :=
  Nat.sInf_le ⟨S, hS, hadm, hm⟩

/--
We call a sequence of integers $0\leq a_1<\cdots <a_k$ admissible if it is missing at least one
congruence class modulo every prime $p$. Let $A(k)=\min a_k$. Estimate $A(k)$ - in particular, is
it true that
$$A(k)\sim k\log k?$$
-/
@[category research open, question, AMS 11]
theorem erdos_1204.parts.i :
    (fun k : ℕ ↦ (A k : ℝ)) ~[atTop] fun k : ℕ ↦ (k : ℝ) * Real.log k := by
  sorry

def erdos_1204.parts.ii.answer : ℕ → ℝ := sorry

/--
We call a sequence of integers $0\leq a_1<\cdots <a_k$ admissible if it is missing at least one
congruence class modulo every prime $p$. Estimate
$$B(k)=\min \frac{a_1+\cdots+a_k}{k}.$$

We read "estimate" as finding an asymptotic formula, since $B(k)\asymp k\log k$ already follows
from the known bounds for $A(k)$ (as $a_j\geq A(j)$).
-/
@[category research open, question value, AMS 11]
theorem erdos_1204.parts.ii : B ~[atTop] erdos_1204.parts.ii.answer := by
  sorry

/--
It is known that $(1/2+o(1))k\log k \leq A(k)$. This lower bound is originally due to Elliott
[El65], but was rediscovered by the Polymath project on bounded gaps between primes [Po14c].
-/
@[category research solved, AMS 11]
theorem erdos_1204.variants.A_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (1 / 2 - ε) * k * Real.log k ≤ (A k : ℝ) := by
  sorry

/--
It is known that $A(k)\leq (1+o(1))k\log k$, by taking the $k$ smallest primes $>k$.
-/
@[category research solved, AMS 11]
theorem erdos_1204.variants.A_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (A k : ℝ) ≤ (1 + ε) * k * Real.log k := by
  sorry

/--
Taking the first $k$ primes which are $>k$ implies $B(k)\leq (1/2+o(1))k\log k$.
-/
@[category research solved, AMS 11]
theorem erdos_1204.variants.B_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, B k ≤ (1 / 2 + ε) * k * Real.log k := by
  sorry

end Erdos1204
