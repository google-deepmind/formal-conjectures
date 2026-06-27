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
# Erdős Problem 281

*References:*
- [erdosproblems.com/281](https://www.erdosproblems.com/281)
- [DaEr36] Davenport, H. and Erdős, P., *On sequences of positive integers*. Acta
  Arithmetica (1936), 147-151.
- [HaRo66] Halberstam, H. and Roth, K. F., *Sequences. Vol. I*. (1966), xx+291.
-/

open Filter Topology

namespace Erdos281

/-- Choices of congruence classes $a_i \pmod{n_i}$. -/
def ResidueChoice (n : ℕ → ℕ) := ∀ i : ℕ, ZMod (n i)

/-- The integers avoiding all congruences $a_i \pmod{n_i}$. -/
def avoidAll (n : ℕ → ℕ) (a : ResidueChoice n) : Set ℤ :=
  {m | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i}

/-- The integers avoiding the first $k$ congruences $a_i \pmod{n_i}$. -/
def avoidPrefix (n : ℕ → ℕ) (a : ResidueChoice n) (k : ℕ) : Set ℤ :=
  {m | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i}

open Classical in
/-- Two-sided natural density sequence for subsets of $\mathbb{Z}$. -/
noncomputable def integerDensitySeq (S : Set ℤ) (N : ℕ) : ℝ :=
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => m ∈ S)).card : ℝ) /
    (2 * (N : ℝ) + 1)

/-- A subset of $\mathbb{Z}$ has two-sided natural density $d$. -/
def HasIntegerDensity (S : Set ℤ) (d : ℝ) : Prop :=
  Tendsto (integerDensitySeq S) atTop (nhds d)

/--
Let $n_1<n_2<\cdots$ be an infinite sequence such that, for any choice of congruence classes
$a_i\pmod{n_i}$, the set of integers not satisfying any of the congruences $a_i\pmod{n_i}$ has
density $0$. Is it true that for every $\epsilon>0$ there exists some $k$ such that, for every
choice of congruence classes $a_i$, the density of integers not satisfying any of the congruences
$a_i\pmod{n_i}$ for $1\leq i\leq k$ is less than $\epsilon$?

The answer is yes; the linked Lean proof formalizes Somani's argument.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos281.lean"]
theorem erdos_281 : answer(True) ↔
    ∀ (n : ℕ → ℕ), StrictMono n → (∀ i, 0 < n i) →
      (∀ a : ResidueChoice n, HasIntegerDensity (avoidAll n a) 0) →
        ∀ ε : ℝ, 0 < ε →
          ∃ k : ℕ, ∀ a : ResidueChoice n,
            ∃ d : ℝ, HasIntegerDensity (avoidPrefix n a k) d ∧ d < ε := by
  sorry

end Erdos281
