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
# Serre's uniformity conjecture over the rationals

Is there a bound $C$, independent of the non-CM elliptic curve $E/\mathbb{Q}$, such that
the Galois action on $E[p]$ is surjective onto $\mathrm{GL}_2(\mathbb{F}_p)$ for every
prime $p > C$? This is the $\mathbb{Q}$ case of Serre's question [Ser72], recalled in
the introduction of [Lem17].

We express surjectivity without choosing a basis: every additive automorphism of $E[p]$
must be induced by an element of $G_{\mathbb{Q}}$. For prime $p$, these automorphisms are
exactly the $\mathbb{F}_p$-linear automorphisms. The non-CM condition uses the classification
of rational CM $j$-invariants.

*References:*
- [Ser72] J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes
  elliptiques*. Inventiones Mathematicae 15 (1972), 259–331.
  https://doi.org/10.1007/BF01405086
- [Lem17] P. Lemos, *Serre's uniformity conjecture for elliptic curves with rational
  cyclic isogenies*, introduction. https://arxiv.org/abs/1702.01985
-/

@[expose] public section

namespace SerreUniformity

/--
The thirteen rational CM $j$-invariants.
-/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736,
    -12288000, 16581375, -884736000, -147197952000, -262537412640768000}

open scoped Classical in
/--
Every additive automorphism of $E[p]$ is induced by a Galois automorphism.
For elliptic $E$ and prime $p$, this means that the mod-$p$ representation is surjective.
-/
def HasFullTorsionAction (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  let T := AddSubgroup.torsionBy (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point (p : ℤ)
  ∀ f : T ≃+ T, ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ P : T, WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom P.val = (f P).val

/--
**Serre's uniformity question over $\mathbb{Q}$** [Ser72, Lem17]: is there a bound
$C$ such that every non-CM elliptic curve over $\mathbb{Q}$ has surjective mod-$p$
Galois representation for every prime $p > C$?
-/
@[category research open, AMS 11 14]
theorem serre_uniformity :
    answer(sorry) ↔
      ∃ C : ℕ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
        ∀ p : ℕ, p.Prime → C < p → HasFullTorsionAction E p := by
  sorry

/--
**Serre's uniformity conjecture over $\mathbb{Q}$, explicit form**: the bound $C = 37$
works, i.e. every non-CM elliptic curve over $\mathbb{Q}$ has surjective mod-$p$ Galois
representation for every prime $p > 37$. From the introduction of [Lem17]: "This conjecture
remains open today, but, over the last forty years, there has been a lot of progress towards
a proof for $K = \mathbb{Q}$ — it is believed that, in this case, $p_K = 37$."
-/
@[category research open, AMS 11 14]
theorem serre_uniformity.variants.bound_37 :
    answer(sorry) ↔
      ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
        ∀ p : ℕ, p.Prime → 37 < p → HasFullTorsionAction E p := by
  sorry

end SerreUniformity
