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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1059

*Reference:* [erdosproblems.com/1059](https://www.erdosproblems.com/1059)
-/

namespace Erdos1059

def isFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial

def factorialsLessThanN (n : ℕ) : Set ℕ :=
  { d | d < n ∧ isFactorial d }

def allFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀d ∈ factorialsLessThanN n, ¬Nat.Prime (n - d)

/-- Are there infinitely many primes $p$ such that $p - k!$ is composite for each $k$ such that $1 ≤ k! < p$? -/
@[category research open, AMS 11]
theorem erdos_1059 :
    Set.Infinite {p | p.Prime ∧ allFactorialSubtractionsComposite p} ↔ answer(sorry) := by
  sorry

@[reducible]
def decidableIsFactorial (d : ℕ) : Prop :=
  ((Finset.Icc 0 d).filter (λ k => Nat.factorial k = d)).Nonempty

def decidableFactorialsLessThanN (n : ℕ) : Finset ℕ :=
  (Finset.Ico 0 n).filter decidableIsFactorial

def decidableAllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ decidableFactorialsLessThanN n, ¬Nat.Prime (n - d)

@[category test, AMS 11]
lemma isFactorial_equivalent (d : ℕ) :
  isFactorial d ↔ decidableIsFactorial d := by
  unfold isFactorial decidableIsFactorial
  simp
  constructor
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter]
    constructor
    · have hk : k <= d := by
        rw [← hk]
        apply Nat.self_le_factorial
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le k, hk⟩
    · exact hk
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter] at hk
    exact hk.2

@[category test, AMS 11]
lemma factorialsLessThanN_equivalent (n : ℕ) :
  factorialsLessThanN n = ↑(decidableFactorialsLessThanN n) := by
  ext d
  unfold factorialsLessThanN decidableFactorialsLessThanN
  simp
  exact λ _ => isFactorial_equivalent d

@[category test, AMS 11]
lemma allFactorialSubtractionsComposite_equivalent (d : ℕ) :
    decidableAllFactorialSubtractionsComposite d ↔ allFactorialSubtractionsComposite d := by
  unfold allFactorialSubtractionsComposite decidableAllFactorialSubtractionsComposite
  rw [factorialsLessThanN_equivalent d]
  simp

@[category test, AMS 11]
theorem allFactorialSubtractionsComposite_101 : allFactorialSubtractionsComposite 101 := by
  have h : decidableAllFactorialSubtractionsComposite 101 := by
    norm_num [decidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 101).mp h

@[category test, AMS 11]
theorem allFactorialSubtractionsComposite_211 : allFactorialSubtractionsComposite 211 := by
  have h : decidableAllFactorialSubtractionsComposite 211 := by
    norm_num [decidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 211).mp h

@[category test, AMS 11]
theorem notAllFactorialSubtractionsComposite_89 : ¬(allFactorialSubtractionsComposite 89) := by
  have h : ¬(decidableAllFactorialSubtractionsComposite 89) := by
    unfold decidableAllFactorialSubtractionsComposite decidableFactorialsLessThanN
    intro h
    specialize h 6
    have : Nat.Prime (89 - 6) := by norm_num
    contradiction
  simp [allFactorialSubtractionsComposite_equivalent] at h
  exact h

@[category test, AMS 11]
theorem testFactorialsLessThanN : factorialsLessThanN 100 = {1, 2, 6, 24} := by
  have h : decidableFactorialsLessThanN 100 = {1, 2, 6, 24} := by
    norm_num [decidableFactorialsLessThanN]
    decide +kernel
  rw [factorialsLessThanN_equivalent]
  simp [h]

end Erdos1059
