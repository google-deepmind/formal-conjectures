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
# Erdős Problem 696

*Reference:* [erdosproblems.com/696](https://www.erdosproblems.com/696)
-/

open scoped Classical

namespace Erdos696

/--
A strictly-increasing chain of natural numbers $d_1 < d_2 < \dots$ such that consecutive
elements satisfy $d_{i+1} \equiv 1 \pmod{d_i}$, and every element divides $n$ and satisfies
the auxiliary predicate $P$.
-/
def ValidChain (n : ℕ) (P : ℕ → Prop) (s : List ℕ) : Prop :=
  s.IsChain (fun a b => a < b ∧ b ≡ 1 [MOD a]) ∧ ∀ d ∈ s, d ∣ n ∧ P d

/--
$h(n)$ is the largest $\ell$ such that there is a sequence of primes $p_1<\cdots < p_\ell$
all dividing $n$ with $p_{i+1}\equiv 1\pmod{p_i}$.
-/
noncomputable def h (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n Nat.Prime s) n

/--
$H(n)$ is the largest $u$ such that there is a sequence of integers $d_1<\cdots < d_u$
all dividing $n$ with $d_{i+1}\equiv 1\pmod{d_i}$.
-/
noncomputable def H (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n (fun _ => True) s) n

/--
Is it true that $H(n)/h(n)\to \infty$ for almost all $n$?

Formalised as: for every threshold $M$, the set of $n$ with $h(n) > 0$ and $H(n)/h(n) > M$
has natural density $1$.
-/
@[category research solved, AMS 11]                     -- was: research open
theorem ratio_to_infinity :
    answer(False) ↔ ∀ M : ℝ,                            -- was: answer(sorry)
      {n : ℕ | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) > M}.HasDensity 1 := by
  sorry

end Erdos696
