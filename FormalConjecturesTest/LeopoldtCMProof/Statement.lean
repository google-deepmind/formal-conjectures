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

public import Mathlib

/-!
# The Leopoldt defect of a number field at a prime `p`

This file formalises the objects of Section 1.1 ("Notations and fundamental facts") of

  Preda Mihăilescu, *On CM `ℤ_p`-extensions and the Leopoldt conjecture for CM fields*,
  arXiv:1105.4544,

which are what the statement of its Theorem 1 refers to.

Following the paper: `E = E(K) = 𝓞(K)ˣ` denotes the units of a number field `K`, and
`P = {℘ ⊂ 𝓞(K) : (p) ⊂ ℘}` the set of primes above `p`.  The paper puts
`K_p = ∏_{℘ ∈ P} K_℘ = K ⊗_ℚ ℚ_p`, lets `ι : K → K_p` be the diagonal embedding and
`U ⊂ K_p^×` be "the group of units, thus the product of local units at the same
completions".  It then defines the `p`-adic closure of the global units as

  `Ē = closure(ι(E)) = ⋂_{n > 0} ι(E) · U^{p^n}`

and the *Leopoldt defect* as

  `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)`.

Leopoldt's conjecture for `K` at `p` is the assertion `𝒟_L(K) = 0`.

Everything lives in the namespace `Leopoldt.Mihailescu`, so that it can be imported next to
the formulations of `FormalConjectures.Wikipedia.LeopoldtConjecture` (namespace `Leopoldt`),
which also has a `LeopoldtConjecture`.
-/

@[expose] public section

namespace Leopoldt.Mihailescu

open NumberField IsDedekindDomain

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]

/-- The set `P = {℘ ⊂ 𝓞(K) : (p) ⊂ ℘}` of primes of `𝓞 K` above `p`. -/
abbrev PrimesOver := {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

instance : Finite (PrimesOver p K) := by
  have hpne : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out (p := p.Prime)).ne_zero
  have hp0 : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  apply Set.Finite.to_subtype
  refine (Ideal.finite_factors (R := 𝓞 K) hp0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)

/-- `U`: the group of semilocal units at `p`, that is the product `∏_{℘ | p} 𝓞_℘^×` of the
local units at the primes above `p`. -/
abbrev SemilocalUnits := ∀ v : PrimesOver p K, (v.1.adicCompletionIntegers K)ˣ

/-- `ι : E(K) → U`, the diagonal embedding of the global units into the semilocal units. -/
noncomputable def diagonalUnits : (𝓞 K)ˣ →* SemilocalUnits p K :=
  MonoidHom.pi fun v => Units.map (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K)).toMonoidHom

/-- `Ē = ⋂_{n > 0} ι(E) · U^{p^n}`, the `p`-adic closure of the image of the global units
inside the semilocal units, exactly as the intersection is written in the source. -/
noncomputable def unitClosure : Subgroup (SemilocalUnits p K) :=
  ⨅ n : ℕ, ((diagonalUnits p K).range ⊔ (powMonoidHom (p ^ (n + 1))).range)

/-- The free `ℤ_p`-rank of a subgroup `H` of a commutative topological group, computed as the
largest `n ≤ bound` for which `ℤ_p^n` admits a continuous injective homomorphism into `H`.

For a closed subgroup of the semilocal units this is the usual free `ℤ_p`-rank: such a subgroup
is isomorphic to `Δ × ℤ_p^d` with `Δ` finite, and continuous injections from `ℤ_p^n` exist
exactly for `n ≤ d`.  Continuity is essential — as abstract groups `ℤ_p^n` embeds into `ℤ_p`
for every `n`; and since `ℤ_p^n` is compact and the target Hausdorff, a continuous injection is
automatically a closed embedding.

The `bound` is carried only so that the supremum is visibly taken over a bounded set and never
falls back on the junk value of `sSup` on an unbounded set of naturals.  Any `bound` at least as
large as the true rank yields the true rank. -/
noncomputable def zpRankBelow {G : Type*} [CommGroup G] [TopologicalSpace G]
    (bound : ℕ) (H : Subgroup G) : ℕ :=
  sSup {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
    Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H}

/-- The **Leopoldt defect** `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)` of `K` at `p`.

`ℤ-rk(E) = r₁ + r₂ - 1` is Dirichlet's unit rank, which Mathlib provides as
`NumberField.Units.rank`.  The `ℤ_p`-rank of `Ē` is bounded by that of the whole semilocal unit
group `U`, which is `[K : ℚ]`, so taking `[K : ℚ]` as the bound never constrains it. -/
noncomputable def defect : ℕ :=
  Units.rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure p K)

/-- `defect` unfolded. Stated here so that downstream files can rewrite with it without
re-elaborating the instance arguments of `zpRankBelow`. -/
theorem defect_eq_sub :
    defect p K = Units.rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := rfl

/-- **Leopoldt's conjecture** for `K` at `p`: the Leopoldt defect vanishes. -/
def LeopoldtConjecture : Prop := defect p K = 0

/-- `LeopoldtConjecture` unfolded. -/
theorem leopoldtConjecture_iff_defect : LeopoldtConjecture p K ↔ defect p K = 0 := Iff.rfl

end Leopoldt.Mihailescu
