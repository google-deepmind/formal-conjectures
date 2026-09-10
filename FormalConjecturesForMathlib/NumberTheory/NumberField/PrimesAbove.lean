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

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

/-!
# The primes of a number field above a rational prime

For a number field `K` and a prime `p`, `NumberField.PrimesAbove K p` is the type of primes
`𝔭` of `𝓞 K` dividing `p`, as a subtype of the height one spectrum, the divisibility `𝔭 ∣ p`
being spelled `(p : 𝓞 K) ∈ 𝔭`. At such a prime the completion `K_𝔭` has residue characteristic
`p`, so `‖p‖ < 1` there; this is recorded as an instance, since it is what gives the principal
units of `K_𝔭` their `ℤ_[p]`-module structure.

The norm on `K_𝔭` detects congruences modulo `𝔭`: mathlib's
`NumberField.FinitePlace.norm_lt_one_iff_mem` says an algebraic integer has norm `< 1` under the
embedding `K → K_𝔭` exactly when it lies in `𝔭`. The two results below restate this for the maps
`ℕ → K_𝔭` and `𝓞 K → K_𝔭`, which is the form needed when working inside `K_𝔭` itself.

## Main definitions

* `NumberField.PrimesAbove K p`: the primes of `𝓞 K` above `p`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.norm_natCast_lt_one`: `‖p‖ < 1` in `K_𝔭` for `𝔭 ∣ p`,
  together with the corresponding `Fact` instance on `NumberField.PrimesAbove`.
* `IsDedekindDomain.HeightOneSpectrum.norm_algebraMap_sub_one_lt`: an algebraic integer `x`
  congruent to `1` modulo `𝔭` satisfies `‖x - 1‖ < 1` in `K_𝔭`, i.e. maps to a principal unit.
-/

open IsDedekindDomain

open scoped NumberField

namespace NumberField

/-- The primes `𝔭` of `𝓞 K` above the rational prime `p`, as a subtype of the height one
spectrum of `𝓞 K`. -/
abbrev PrimesAbove (K : Type*) [Field K] [NumberField K] (p : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

end NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem norm_natCast_lt_one {p : ℕ} (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    ‖((p : ℕ) : v.adicCompletion K)‖ < 1 := by
  rw [← map_natCast' (algebraMap (𝓞 K) (adicCompletion K v)) rfl _]
  exact (NumberField.FinitePlace.norm_lt_one_iff_mem _ _ _).2 hv

theorem norm_algebraMap_sub_one_lt {x : 𝓞 K} (hx : x - 1 ∈ v.asIdeal) :
    ‖algebraMap (𝓞 K) (v.adicCompletion K) x - 1‖ < 1 := by
  rw [← map_one (algebraMap (𝓞 K) (v.adicCompletion K)), ← map_sub]
  exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v _).2 hx

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField

/-- Each `K_𝔭` with `𝔭 ∣ p` has residue characteristic `p`. This is the instance that gives the
principal units of `K_𝔭` their `ℤ_[p]`-module structure. -/
instance (K : Type*) [Field K] [NumberField K] (p : ℕ) (v : PrimesAbove K p) :
    Fact (‖((p : ℕ) : v.1.adicCompletion K)‖ < 1) :=
  ⟨v.1.norm_natCast_lt_one v.2⟩

end NumberField
