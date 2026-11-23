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
# Stern Primes

As recounted by Laurent Hodges (1993), Christian Goldbach proposed in a 1752 letter to Euler that
every odd integer greater than $1$ equals $p + 2 b^2$ with $b \ge 0$ (counting $1$ as prime); for
modern primes, its nontrivial content is the *Goldbach–Stern conjecture* that every odd composite
equals $p + 2 b^2$ with $p$ prime and $b \ge 1$. Moritz Abraham Stern (1856) refuted this via the
counterexamples $5777$ and $5993$ (`OEIS A060003`).

A prime $q$ admitting no decomposition $q = p + 2 b^2$ with $p$ prime and $b \ge 1$ is called a
*Stern prime* (`OEIS A042978`). Only eight examples are known ($2, 3, 17, 137, 227, 977, 1187$, and
$1493$); Euler noted heuristically that larger primes acquire more decompositions $p + 2 b^2$,
suggesting that Stern primes form a finite set and that $1493$ may be the largest.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Stern_prime)
- [OEIS A042978](https://oeis.org/A042978)
- M. A. Stern, *Sur une assertion de Goldbach relative aux nombres impairs*, Nouv. Ann. Math.
  **15** (1856), 23–24.
- L. Hodges, *A lesser-known Goldbach conjecture*, Math. Mag. **66** (1993), no. 1, 45–47.
-/

@[expose] public section

namespace SternPrime

/-- Predicate asserting that $n = p + 2 b^2$ for some prime $p$ and integer $b \ge 1$. -/
def HasPrimePlusTwiceSquare (n : ℕ) : Prop :=
  ∃ p b : ℕ, p.Prime ∧ 1 ≤ b ∧ n = p + 2 * b ^ 2

/-- Predicate asserting that $q$ is prime and fails `HasPrimePlusTwiceSquare`. -/
def IsSternPrime (q : ℕ) : Prop :=
  q.Prime ∧ ¬ HasPrimePlusTwiceSquare q

instance (n : ℕ) : Decidable (HasPrimePlusTwiceSquare n) :=
  decidable_of_iff (∃ b < n.sqrt + 1, 1 ≤ b ∧ 2 * b ^ 2 < n ∧ (n - 2 * b ^ 2).Prime) <| by
    unfold HasPrimePlusTwiceSquare
    constructor
    · rintro ⟨b, _, hb, hlt, hp⟩
      exact ⟨n - 2 * b ^ 2, b, hp, hb, by omega⟩
    · rintro ⟨p, b, hp, hb, rfl⟩
      have hp_pos : 0 < p := hp.pos
      have hb_sqrt : b ≤ (p + 2 * b ^ 2).sqrt := Nat.le_sqrt.mpr (by nlinarith)
      exact ⟨b, by omega, hb, by omega, by simpa using hp⟩

instance (q : ℕ) : Decidable (IsSternPrime q) :=
  inferInstanceAs (Decidable (q.Prime ∧ ¬ HasPrimePlusTwiceSquare q))

/-- Verifies that all eight known examples $2, 3, 17, 137, 227, 977, 1187, 1493$ are Stern
primes. -/
@[category test, AMS 11]
theorem isSternPrime_known_examples :
    ∀ q ∈ ([2, 3, 17, 137, 227, 977, 1187, 1493] : List ℕ), IsSternPrime q := by
  decide +kernel

/-- Checks that $5 = 3 + 2 \cdot 1^2$ and $11 = 3 + 2 \cdot 2^2$ satisfy `HasPrimePlusTwiceSquare`
and hence are not Stern primes. -/
@[category test, AMS 11]
theorem not_isSternPrime_five_and_eleven :
    HasPrimePlusTwiceSquare 5 ∧ HasPrimePlusTwiceSquare 11 ∧
      ¬ IsSternPrime 5 ∧ ¬ IsSternPrime 11 := by
  have h5 : HasPrimePlusTwiceSquare 5 := ⟨3, 1, by norm_num, by omega, by norm_num⟩
  have h11 : HasPrimePlusTwiceSquare 11 := ⟨3, 2, by norm_num, by omega, by norm_num⟩
  exact ⟨h5, h11, fun h => h.2 h5, fun h => h.2 h11⟩

/--
Is the set of Stern primes finite? Euler's representation heuristic suggests that only finitely
many primes avoid the form $p + 2 b^2$.
-/
@[category research open, question, AMS 11]
theorem stern_primes_finite : {q : ℕ | IsSternPrime q}.Finite := by
  sorry

/--
Does $\{2, 3, 17, 137, 227, 977, 1187, 1493\}$ exhaust all Stern primes? No ninth example appears
among the first $100{,}000$ primes (McCranie) or below $2 \times 10^{13}$ (Chaffin, `OEIS A042978`).
-/
@[category research open, question, AMS 11]
theorem isSternPrime_iff :
    ∀ q : ℕ, IsSternPrime q ↔ q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) := by
  sorry

end SternPrime
