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
# Newman's Conjecture

*References:*
[Wikipedia](https://en.wikipedia.org/wiki/Newman%27s_conjecture)
[MathWorld](https://mathworld.wolfram.com/NewmansConjecture.html)
[Arxiv](https://arxiv.org/pdf/math/0008140)
-/

@[expose] public section

namespace NewmanConjecture

/--
Newman's Conjecture: For each residue class $r$ of any positive integer $m$ there are
infinitely many nonnegative integers such that $p(n) \equiv r \pmod m$.
-/
@[category research open, AMS 5 11]
theorem newman_conjecture (m r : ℕ) (hr : r < m) :
  Infinite {n : ℕ | Nat.partitionNumber n % m = r} := by
  sorry

/--
Newman's Conjecture implies Erdős : For every prime $m$ there exists some $n$ such that
$m | p(n)$.
-/
@[category textbook, AMS 5 11]
theorem newman_implies_erdos (m : ℕ) (hm : m.Prime) (P: type_of% newman_conjecture) :
  ¬ IsEmpty {n : ℕ | Nat.partitionNumber n % m = (0 : ℕ)} := by

  specialize P m 0 (Nat.Prime.pos hm)
  intro h_contra
  exact IsEmpty.false (Classical.choice P.nonempty)

/--
Newman's Conjecture implies Erdős–Ivić : There exist infinitely many primes $m$ such that
for some $n > 0, m | p(n)$.
-/
@[category textbook, AMS 5 11]
theorem newman_implies_erdos_ivic' (P: type_of% newman_conjecture) :
  Infinite {m : ℕ | m.Prime ∧ ¬ IsEmpty {n : ℕ | Nat.partitionNumber n % m = (0 : ℕ)}} := by

  rw [← not_finite_iff_infinite]
  intro hfin
  obtain ⟨B, hB⟩ := (Set.finite_coe_iff.mp hfin).bddAbove
  obtain ⟨m, hm_ge, hm_prime⟩ := Nat.exists_infinite_primes (B + 1)
  have h_infinite_primes := P m 0 hm_prime.pos
  have hm_le_B : m ≤ B := hB ⟨hm_prime, not_isEmpty_iff.mpr inferInstance⟩
  linarith
end NewmanConjecture
