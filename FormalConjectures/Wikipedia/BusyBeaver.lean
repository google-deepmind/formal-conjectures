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

universe u v

open Turing BusyBeaver

namespace BusyBeaver

structure Candidate (n : ℕ) where
  Γ : Type
  Λ : Type
  Γ_fintype : Fintype Γ
  Γ_card : Fintype.card Γ = n
  Γ_inhabited : Inhabited Γ
  Λ_fintype : Fintype Λ
  Λ_card : Fintype.card Λ = 2
  Λ_inhabited : Inhabited Λ
  M : Machine Γ Λ
  M_isHalting : M.IsHalting

instance {n : ℕ} {M : Candidate n} : Fintype M.Γ := M.Γ_fintype
instance {n : ℕ} {M : Candidate n} : Fintype M.Λ := M.Λ_fintype
instance {n : ℕ} {M : Candidate n} : Inhabited M.Γ := M.Γ_inhabited
instance {n : ℕ} {M : Candidate n} : Inhabited M.Λ := M.Λ_inhabited

/--
`BB(n)` is the `n`-th Busy Beaver number.
*This is the maximum shifts function*, not the "number of ones function"
-/
noncomputable def BB (n : ℕ) : ℕ :=
  sSup { N | ∃ C : Candidate n, C.M.haltingNumber = N}

end BusyBeaver

open BusyBeaver

/--
To compute `BB n`, we need only consider machines with states and symbols indexed in `Fin`.
-/
@[category API, AMS 3]
theorem sanity_check (n : ℕ) [NeZero n] :
    BB n = sSup {N | ∃ (M : Machine (Fin n) (Fin 2)) (_ : M.IsHalting),
      M.haltingNumber = N} := by
  sorry

@[category test, AMS 3]
theorem BB_1 : BB 1 = 1 := by
  sorry

@[category undergraduate, AMS 3]
theorem BB_2 : BB 2 = 6 := by
  sorry

@[category undergraduate, AMS 3]
theorem BB_3 : BB 3 = 21 := by
  sorry

@[category undergraduate, AMS 3]
theorem BB_4 : BB 4 = 107 := by
  sorry

@[category research solved, AMS 3]
theorem BB_5 : BB 5 = 47176870 := by
  sorry
