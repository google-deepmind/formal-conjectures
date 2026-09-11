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

import FormalConjecturesUtil

/-!
# Erdős Problem 696

*Reference:* [erdosproblems.com/696](https://www.erdosproblems.com/696)
-/

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
noncomputable def h (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n Nat.Prime s) n

/--
$H(n)$ is the largest $u$ such that there is a sequence of integers $d_1<\cdots < d_u$
all dividing $n$ with $d_{i+1}\equiv 1\pmod{d_i}$.
-/
noncomputable def H (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n (fun _ => True) s) n

/-- The prime-chain definition has the expected value at $n = 1$. -/
@[category test, AMS 11]
theorem h_one : h 1 = 0 := by
  classical
  rw [h, Nat.findGreatest_eq_zero_iff]
  intro k hk hk_le
  have hk_eq : k = 1 := by omega
  subst k
  rintro ⟨s, hslen, hvalid⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hslen
  rw [ValidChain] at hvalid
  have hp := hvalid.2 p (by simp)
  have hp_one : p = 1 := Nat.dvd_one.mp hp.1
  subst p
  exact Nat.not_prime_one hp.2

/--
Is it true that $H(n)/h(n)\to \infty$ for almost all $n$?

Formalised as: for every threshold $M$, the set of $n$ with $h(n) > 0$ and $H(n)/h(n) > M$
has natural density $1$. This is false: in fact, $H(n)/h(n) = 2 + o(1)$ for almost all $n$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/davidturturean/erdos-696/blob/4fa1bf2c6ff6f2e0c7024f814614c7455404fdd3/Erdos696/Main.lean#L35"]
theorem erdos_696 :
    answer(False) ↔ ∀ M : ℝ,
      {n : ℕ | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) > M}.HasDensity 1 := by
  sorry

end Erdos696
