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
# Ben Green's Open Problem 96

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.96)
- [KK07] Kahane, J.-P. and Katznelson, Y., *Entiers aléatoires, ensembles de Sidon, densité dans
  le groupe de Bohr et ensembles d'analyticité*. Note, with an abridged English version (2007).
  [arXiv:0705.4261](https://arxiv.org/abs/0705.4261)
- [KK08] Kahane, J.-P. and Katznelson, Y., *Entiers aléatoires et analyse harmonique*.
  J. Anal. Math. 105 (2008), 363--378.
- [Pi83] Pisier, G., *Arithmetic characterizations of Sidon sets*.
  Bull. Amer. Math. Soc. (N.S.) 8 (1983), no. 1, 87--89.
-/

@[expose] public section

open MeasureTheory

namespace Green96

/--
`fourierAlgebra Λ` is the Fourier algebra $A(\Lambda) = \{(\hat f(\lambda))_{\lambda \in \Lambda} :
f \in L^1(\mathbb{T})\}$, a set of functions $\Lambda \to \mathbb{C}$. Here
$\mathbb{T}$ is `AddCircle (1 : ℝ)` with the Haar probability measure `AddCircle.haarAddCircle`
and $\hat f(n)$ is `fourierCoeff f n`.
-/
def fourierAlgebra (Λ : Set ℤ) : Set (Λ → ℂ) :=
  {g | ∃ f : AddCircle (1 : ℝ) → ℂ, Integrable f AddCircle.haarAddCircle ∧
    ∀ l : Λ, g l = fourierCoeff f (l : ℤ)}

/--
$\Lambda \subset \mathbb{Z}$ is a Sidon set (in the sense of harmonic analysis) if $A(\Lambda)$
coincides with $c_0(\Lambda)$, the sequences on $\Lambda$ tending to zero at infinity (that is,
along the cofinite filter on $\Lambda$). Finite sets are Sidon.
-/
def IsSidon (Λ : Set ℤ) : Prop :=
  fourierAlgebra Λ = {g : Λ → ℂ | Filter.Tendsto g Filter.cofinite (nhds 0)}

/--
A function $F : \mathbb{R} \to \mathbb{C}$ operates on $A(\Lambda)$ if $F \circ \varphi \in
A(\Lambda)$ for every real-valued $\varphi \in A(\Lambda)$. [KK07] say "every function $F$ defined
on $\mathbb{R}$"; we take $F$ complex-valued.
-/
def Operates (Λ : Set ℤ) (F : ℝ → ℂ) : Prop :=
  ∀ φ ∈ fourierAlgebra Λ, (∀ l, (φ l).im = 0) →
    (fun l => F (φ l).re) ∈ fourierAlgebra Λ

/--
$\Lambda \subset \mathbb{Z}$ is a set of analyticity if only analytic functions operate on
$A(\Lambda)$, that is, every $F : \mathbb{R} \to \mathbb{C}$ operating on $A(\Lambda)$ is analytic
in some neighbourhood of $0$ (`AnalyticAt ℝ F 0`). A finite $\Lambda$ is not a set of
analyticity, since then $A(\Lambda)$ is all of $\mathbb{C}^\Lambda$ and every $F$ operates.
-/
def IsSetOfAnalyticity (Λ : Set ℤ) : Prop :=
  ∀ F : ℝ → ℂ, Operates Λ F → AnalyticAt ℝ F 0

/--
Is every set $\Lambda \subset \mathbb{Z}$ either a Sidon set, or a set of analyticity?

This is the Dichotomy Problem. As [Gr24] stresses, "Sidon" is the harmonic-analysis notion:
$\Lambda$ is Sidon if and only if $A(\Lambda) = c_0(\Lambda)$, and $\Lambda$ is a set of analyticity
if only analytic functions $F$ act on $A(\Lambda)$. We use the definition of [KK07]: "$\Lambda$ is a
set of analyticity if only analytic functions operate in $A(\Lambda)$, that is, every function $F$
defined on $\mathbb{R}$ such that $F \circ \varphi \in A(\Lambda)$ for every real-valued
$\varphi \in A(\Lambda)$ is analytic in some neighborhood of $0$." No set is both: [KK07] notes that
Sidon sets are not sets of analyticity. For more on the problem [Gr24] recommends [KK08].
-/
@[category research open, question, AMS 42 43]
theorem green_96 : ∀ Λ : Set ℤ, IsSidon Λ ∨ IsSetOfAnalyticity Λ := by
  sorry

/--
A set $A \subset \mathbb{Z}$ is independent if all its finite subset sums are distinct (for
example, the powers of two): distinct finite subsets of $A$ have distinct sums. In particular
$0 \notin A$ (the sum over $\{0\}$ equals the empty sum).
-/
def IsIndependent (A : Set ℤ) : Prop :=
  ∀ S T : Finset ℤ, (S : Set ℤ) ⊆ A → (T : Set ℤ) ⊆ A → ∑ x ∈ S, x = ∑ x ∈ T, x → S = T

/--
[Gr24] also asks: "a beautiful open question is whether every Sidon subset of $\mathbb{Z}$ (in the
commutative harmonic analysis sense) is a finite union of independent sets, that is to say sets
$A \subset \mathbb{Z}$, all of whose finite subset sums are distinct (for example, the powers of
two)." Green notes that [Pi83] showed that $S \subset \mathbb{Z}$ is Sidon if and only if there is a
$\delta > 0$ such that every finite $S' \subset S$ contains an independent set $A$ with
$|A| \geq \delta |S'|$.

We assume $0 \notin \Lambda$: no independent set contains $0$, while $\{0\}$ is a Sidon set, so
without this hypothesis the answer would be no for a trivial reason.
-/
@[category research open, question, AMS 5 42 43]
theorem green_96.variants.finite_union_independent :
    ∀ Λ : Set ℤ, (0 : ℤ) ∉ Λ → IsSidon Λ →
      ∃ (n : ℕ) (A : Fin n → Set ℤ), (∀ i, IsIndependent (A i)) ∧ Λ = ⋃ i, A i := by
  sorry

end Green96
