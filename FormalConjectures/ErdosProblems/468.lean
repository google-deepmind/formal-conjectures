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
# Erdős Problem 468

*References:*
- [erdosproblems.com/468](https://www.erdosproblems.com/468)
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monogr. Enseign. Math. 28 (1980), p. 93.
-/

@[expose] public section

namespace Erdos468

/-- The divisors of $n$ satisfying $1 < d \leq t$. -/
def initialDivisors (n t : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => 1 < d ∧ d ≤ t)

/-- The sum of all nonunit divisors of $n$ through $t$. -/
def prefixSum (n t : ℕ) : ℕ := ∑ d ∈ initialDivisors n t, d

/-- The nonempty initial sums of the increasing list of divisors of $n$ greater than $1$.
The divisor $n$ is included. -/
def D (n : ℕ) : Finset ℕ :=
  (n.divisors.filter (fun d => 1 < d)).image (prefixSum n)

/-- All values occurring at an index smaller than $n$. -/
def earlierValues (n : ℕ) : Finset ℕ := (Finset.range n).biUnion D

/-- The values occurring for the first time at index $n$. -/
def newValues (n : ℕ) : Finset ℕ := D n \ earlierValues n

/-- The size of $D_n \setminus \bigcup_{m<n} D_m$. -/
def newCount (n : ℕ) : ℕ := (newValues n).card

/-- A value is representable if it belongs to some $D_n$. -/
def Representable (N : ℕ) : Prop := ∃ n : ℕ, N ∈ D n

/-- The least index at which a representable value occurs.
A proof of representability is required because some values have no preimage. -/
noncomputable def f (N : ℕ) (h : Representable N) : ℕ := Nat.find h

/-- There is a preimage of $N$ at most $\varepsilon N$. -/
def SmallWitness (N : ℕ) (ε : ℝ) : Prop :=
  ∃ n : ℕ, N ∈ D n ∧ (n : ℝ) ≤ ε * (N : ℝ)

@[category API, AMS 11]
theorem mem_D {n N : ℕ} : N ∈ D n ↔
    ∃ t : ℕ, t ∣ n ∧ n ≠ 0 ∧ 1 < t ∧ prefixSum n t = N := by
  simp only [D, Finset.mem_image, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨t, ⟨⟨ht, hn⟩, hpos⟩, he⟩
    exact ⟨t, ht, hn, hpos, he⟩
  · rintro ⟨t, ht, hn, hpos, he⟩
    exact ⟨t, ⟨⟨ht, hn⟩, hpos⟩, he⟩

@[category API, AMS 11]
theorem f_mem (N : ℕ) (h : Representable N) : N ∈ D (f N h) := Nat.find_spec h

@[category API, AMS 11]
theorem f_le {N n : ℕ} (h : Representable N) (hn : N ∈ D n) : f N h ≤ n :=
  Nat.find_min' h hn

@[category API, AMS 11]
theorem smallWitness_iff_f {N : ℕ} (h : Representable N) (ε : ℝ) :
    SmallWitness N ε ↔ (f N h : ℝ) ≤ ε * (N : ℝ) := by
  constructor
  · rintro ⟨n, hn, hbound⟩
    exact le_trans (by exact_mod_cast f_le h hn) hbound
  · intro hbound
    exact ⟨f N h, f_mem N h, hbound⟩

@[category test, AMS 11]
theorem D_zero : D 0 = ∅ := by simp [D]

@[category test, AMS 11]
theorem D_one : D 1 = ∅ := by simp [D]

@[category test, AMS 11]
theorem D_four : D 4 = {2, 6} := by decide

@[category test, AMS 11]
theorem D_twelve : D 12 = {2, 5, 9, 15, 27} := by decide

@[category test, AMS 11]
theorem newCount_twelve : newCount 12 = 3 := by decide

/-- For any $n$ let $D_n$ be the set of sums of the shape
$d_1,d_1+d_2,d_1+d_2+d_3,\ldots$ where $1<d_1<d_2<\cdots$ are the divisors of $n$.
What is the size of $D_n\backslash \cup_{m<n}D_m$? -/
@[category research open, AMS 11]
theorem erdos_468.parts.i : newCount = answer(sorry) := by
  sorry

/-- If $f(N)$ is the minimal $n$ such that $N\in D_n$ then is it true that $f(N)=o(N)$?

The witness formulation requires eventual representability and avoids assigning a value to
$f(N)$ when $N$ has no preimage. -/
@[category research open, AMS 11]
theorem erdos_468.parts.ii :
    answer(sorry) ↔ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → SmallWitness N ε := by
  sorry

/-- Perhaps just for almost all $N$?

This asks whether $f(N)=o(N)$ outside a single exceptional set of natural density zero. -/
@[category research open, AMS 11]
theorem erdos_468.parts.iii :
    answer(sorry) ↔ ∃ E : Set ℕ, E.HasDensity 0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → N ∉ E → SmallWitness N ε := by
  sorry

end Erdos468
