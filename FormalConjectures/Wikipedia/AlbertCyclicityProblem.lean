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
# Albert's cyclicity problem for prime-degree division algebras

Over a base field $K$, let $D$ be a finite-dimensional central division $K$-algebra of degree $n$,
so $\dim_K D = n^2$. By [GS17, Proposition 2.5.2], $D$ is a *cyclic algebra* over $K$ precisely
when $D$ embeds a cyclic Galois field extension $L / K$ of degree $[L : K] = n$.

Every central division algebra of degree $2$ (a quaternion division algebra) is cyclic, and
Wedderburn [We21] and Albert [Al39, Chapter XI] proved that every central division algebra of
degree $3$ is cyclic. By contrast, Albert constructed non-cyclic division algebras of composite
degree $4$. Albert's cyclicity problem asks whether every prime-degree central division algebra
with degree $p \ge 5$ over an arbitrary base field $K$ must be cyclic.

*References:*
- [Wikipedia: Brauer group](https://en.wikipedia.org/wiki/Brauer_group#Cyclic_algebras)
- [We21] J. H. M. Wedderburn, *On division algebras*, Trans. Amer. Math. Soc. **22** (1921),
  129–135.
- [Al39] A. A. Albert, *Structure of Algebras*, AMS Colloquium Publications **24**, Amer. Math.
  Soc., 1939.
- [GS17] P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, 2nd ed.,
  Cambridge Studies in Advanced Mathematics **165**, Cambridge Univ. Press, 2017.
-/

@[expose] public section

namespace AlbertCyclicityProblem

universe u

/-- A finite-dimensional division $K$-algebra $D$ is *cyclic* if it admits a $K$-algebra
embedding from a finite cyclic Galois extension $L / K$ satisfying $[L : K]^2 = [D : K]$
(a cyclic maximal subfield; see [GS17, Proposition 2.5.2]). -/
def IsCyclicDivisionAlgebra (K : Type u) [Field K] (D : Type u) [DivisionRing D]
    [Algebra K D] : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
    Nonempty (L →ₐ[K] D) ∧
    IsGalois K L ∧
    IsCyclic (L ≃ₐ[K] L) ∧
    Module.finrank K L ^ 2 = Module.finrank K D

/-- Every field $K$ is a degree-$1$ cyclic division algebra over itself. -/
@[category test, AMS 12 16]
theorem isCyclicDivisionAlgebra_self (K : Type u) [Field K] :
    IsCyclicDivisionAlgebra K K := by
  refine ⟨K, inferInstance, inferInstance, inferInstance, ⟨AlgHom.id K K⟩, inferInstance, ?_,
    by simp [Module.finrank_self]⟩
  refine ⟨⟨1, fun g => ⟨0, ?_⟩⟩⟩
  ext x
  simpa using (AlgEquiv.commutes g x).symm

/-- `IsCyclicDivisionAlgebra` is preserved under $K$-algebra isomorphism. -/
@[category API, AMS 12 16]
theorem isCyclicDivisionAlgebra_of_algEquiv {K D₁ D₂ : Type u} [Field K]
    [DivisionRing D₁] [DivisionRing D₂] [Algebra K D₁] [Algebra K D₂]
    (e : D₁ ≃ₐ[K] D₂) (h : IsCyclicDivisionAlgebra K D₁) :
    IsCyclicDivisionAlgebra K D₂ := by
  rcases h with ⟨L, hF, hA, hFD, ⟨g⟩, hGal, hCyc, hdim⟩
  refine ⟨L, hF, hA, hFD, ⟨e.toAlgHom.comp g⟩, hGal, hCyc, ?_⟩
  rwa [← LinearEquiv.finrank_eq e.toLinearEquiv]

/-- Because $\dim_{\mathbb{R}} \mathbb{C} = 2$ is not a square, $\mathbb{C}$ is not a cyclic
division algebra over $\mathbb{R}$. -/
@[category test, AMS 12 16]
theorem not_isCyclicDivisionAlgebra_real_complex :
    ¬ IsCyclicDivisionAlgebra ℝ ℂ := by
  rintro ⟨L, hFL, hAL, _, _, _, _, hdim⟩
  let _ := hFL
  let _ := hAL
  rw [Complex.finrank_real_complex] at hdim
  have hn : Module.finrank ℝ L ≤ 2 := by nlinarith
  interval_cases (Module.finrank ℝ L) <;> omega

/-- Every central division $K$-algebra of degree $2$ ($\dim_K D = 4$, i.e. a quaternion division
algebra) is cyclic [Al39]. -/
@[category textbook, AMS 12 16]
theorem degree_two_isCyclicDivisionAlgebra
    (K D : Type) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D]
    (hdim : Module.finrank K D = 4) :
    IsCyclicDivisionAlgebra K D := by
  sorry

/-- **Wedderburn–Albert degree-$3$ theorem**: every central division $K$-algebra of degree $3$
($\dim_K D = 9$) is cyclic (proved by Wedderburn [We21] for $\operatorname{char} K \neq 3$ and
by Albert [Al39, Chapter XI] in characteristic $3$). -/
@[category research solved, AMS 12 16]
theorem wedderburn_albert_degree_three_cyclic
    (K D : Type) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D]
    (hdim : Module.finrank K D = 9) :
    IsCyclicDivisionAlgebra K D := by
  sorry

/-- **Albert's cyclicity problem**: is every prime-degree central division $K$-algebra $D$ with
prime degree $p \ge 5$ ($\dim_K D = p^2$) a cyclic division algebra? -/
@[category research open, question, AMS 12 16]
theorem albert_cyclicity_problem :
    ∀ (p : ℕ), p.Prime → 5 ≤ p →
      ∀ (K D : Type) [Field K] [DivisionRing D] [Algebra K D]
        [Algebra.IsCentral K D] [FiniteDimensional K D],
        Module.finrank K D = p ^ 2 → IsCyclicDivisionAlgebra K D := by
  sorry

/-- Characteristic-zero specialization of `albert_cyclicity_problem` [GS17] (not stated
separately on Wikipedia): is every prime-degree central division $K$-algebra with prime degree
$p \ge 5$ and $\operatorname{char} K = 0$ cyclic? Compare also
`SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast` for the single-symbol
question over $\mathbb{C}(x_1, x_2)$. -/
@[category research open, question, AMS 12 16]
theorem albert_cyclicity_problem.variants.char_zero :
    ∀ (p : ℕ), p.Prime → 5 ≤ p →
      ∀ (K D : Type) [Field K] [CharZero K] [DivisionRing D] [Algebra K D]
        [Algebra.IsCentral K D] [FiniteDimensional K D],
        Module.finrank K D = p ^ 2 → IsCyclicDivisionAlgebra K D := by
  sorry

end AlbertCyclicityProblem
