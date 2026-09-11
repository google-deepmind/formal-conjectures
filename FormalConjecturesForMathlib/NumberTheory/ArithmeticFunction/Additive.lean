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

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

@[expose] public section

/-!
# Additive arithmetic functions

An arithmetic function `f` is *additive* if `f 1 = 0` and `f (m * n) = f m + f n` whenever `m`
and `n` are coprime, *completely additive* if the latter holds for all nonzero `m` and `n`, and
*strongly additive* if it is additive and `f (p ^ k) = f p` for every prime `p` and every `k ≠ 0`.

These are the additive counterparts of `ArithmeticFunction.IsMultiplicative`, and follow the
same conventions: as there, the value at `1` is part of the definition.
-/

namespace ArithmeticFunction

variable {R : Type*} [AddMonoid R]

/-- Additive functions -/
def IsAdditive (f : ArithmeticFunction R) : Prop :=
  f 1 = 0 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n

/-- Completely additive functions -/
def IsCompletelyAdditive (f : ArithmeticFunction R) : Prop :=
  f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

/-- Strongly additive functions: additive functions with `f (p ^ k) = f p` for every prime `p`
and every `k ≠ 0`. -/
def IsStronglyAdditive (f : ArithmeticFunction R) : Prop :=
  f.IsAdditive ∧ ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

namespace IsAdditive

variable {f : ArithmeticFunction R}

@[simp]
theorem map_one (h : f.IsAdditive) : f 1 = 0 :=
  h.1

@[simp]
theorem map_mul_of_coprime (hf : f.IsAdditive) {m n : ℕ} (h : m.Coprime n) :
    f (m * n) = f m + f n :=
  hf.2 h

end IsAdditive

namespace IsCompletelyAdditive

variable {f : ArithmeticFunction R}

@[simp]
theorem map_one (h : f.IsCompletelyAdditive) : f 1 = 0 :=
  h.1

theorem map_mul (hf : f.IsCompletelyAdditive) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    f (m * n) = f m + f n :=
  hf.2 hm hn

theorem isAdditive (hf : f.IsCompletelyAdditive) : f.IsAdditive := by
  refine ⟨hf.map_one, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    simp [hmn, hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    simp [hmn, hf.map_one]
  exact hf.map_mul hm hn

theorem map_pow (hf : f.IsCompletelyAdditive) {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    f (m ^ k) = k • f m := by
  induction k with
  | zero => simp [hf.map_one]
  | succ k ih => rw [pow_succ, hf.map_mul (pow_ne_zero _ hm) hm, ih, succ_nsmul]

theorem map_prime_pow (hf : f.IsCompletelyAdditive) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ k) = k • f p :=
  hf.map_pow hp.ne_zero k

end IsCompletelyAdditive

namespace IsStronglyAdditive

variable {f : ArithmeticFunction R}

theorem isAdditive (hf : f.IsStronglyAdditive) : f.IsAdditive :=
  hf.1

theorem map_prime_pow (hf : f.IsStronglyAdditive) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    f (p ^ k) = f p :=
  hf.2 hp hk

end IsStronglyAdditive

end ArithmeticFunction
