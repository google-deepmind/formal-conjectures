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

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Lattice

@[expose] public section

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `n = 1`. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactorsList.getLastI

@[simp]
lemma maxPrimeFac_zero :
    maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac, List.getLastI]

@[simp]
lemma maxPrimeFac_one :
    maxPrimeFac 1 = 0 := by
  simp [maxPrimeFac, List.getLastI]

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Prime (maxPrimeFac n) := by
  have hn : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Prime (n.primeFactorsList.getLast hn) := prime_of_mem_primeFactorsList hmem
  simpa [maxPrimeFac, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hn] using hprime

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  refine le_antisymm h_le ?_
  have hmem : p ∈ n.primeFactorsList := (mem_primeFactorsList hn.ne').2 ⟨hp, h_dvd⟩
  have hp_last : p ≤ n.primeFactorsList.getLast (List.ne_nil_of_mem hmem) :=
    (primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxPrimeFac, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil (List.ne_nil_of_mem hmem)] using hp_last

@[simp]
lemma one_lt_maxPrimeFac_iff (n : ℕ) :
    1 < maxPrimeFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat
