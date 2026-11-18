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

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Primitive Prime Divisors of Sequences

A prime $p$ is a *primitive prime divisor* of the $n$-th term $W_n$ of a sequence if $p \mid W_n$
and $p \nmid W_k$ for all $1 \le k < n$.
-/

@[expose] public section

/-- A prime `p : ℕ` is a *primitive prime divisor* of `W n` if `p` divides `W n` and `p` does not
divide `W k` for any `1 ≤ k < n`. -/
def IsPrimitivePrimeDivisor {α β : Type*} [NatCast α] [NatCast β] [Dvd β]
    (W : α → β) (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ (p : β) ∣ W n ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ ((p : β) ∣ W k)

/-- `W n` has a *primitive prime divisor* if some prime `p : ℕ` divides `W n` without dividing
`W k` for any `1 ≤ k < n`. -/
def HasPrimitivePrimeDivisor {α β : Type*} [NatCast α] [NatCast β] [Dvd β]
    (W : α → β) (n : ℕ) : Prop :=
  ∃ p : ℕ, IsPrimitivePrimeDivisor W n p

namespace IsPrimitivePrimeDivisor

variable {α β : Type*} [NatCast α] [NatCast β] [Dvd β] {W : α → β} {m n p q : ℕ}

theorem prime (h : IsPrimitivePrimeDivisor W n p) : p.Prime :=
  h.1

theorem dvd (h : IsPrimitivePrimeDivisor W n p) : (p : β) ∣ W n :=
  h.2.1

theorem not_dvd (h : IsPrimitivePrimeDivisor W n p) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    ¬ ((p : β) ∣ W k) :=
  h.2.2 k hk1 hkn

theorem hasPrimitivePrimeDivisor (h : IsPrimitivePrimeDivisor W n p) :
    HasPrimitivePrimeDivisor W n :=
  ⟨p, h⟩

theorem ne_of_lt (hm : 1 ≤ m) (hmn : m < n)
    (hp : IsPrimitivePrimeDivisor W m p) (hq : IsPrimitivePrimeDivisor W n q) : p ≠ q := by
  rintro rfl
  exact hq.not_dvd hm hmn hp.dvd

end IsPrimitivePrimeDivisor
