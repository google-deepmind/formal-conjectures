import Mathlib

open Classical Finset SimpleGraph MeasureTheory

namespace SidorenkoConjecture


/-- The unit interval `[0, 1]`. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/--
A **graphon** is a symmetric, measurable function `W : [0, 1] × [0, 1] → [0, 1]`.
The domain is the unit interval squared, and the image is contained in the unit interval.
-/
structure Graphon where
  toFun : UnitInterval × UnitInterval → UnitInterval
  measurable : Measurable toFun
  symmetric : ∀ x y : UnitInterval, toFun (x, y) = toFun (y, x)

instance : CoeFun Graphon (fun _ => UnitInterval × UnitInterval → UnitInterval) := ⟨Graphon.toFun⟩

namespace Graphon

/-- Extensionality principle for `Graphon`. -/
@[ext]
theorem ext {W₁ W₂ : Graphon} (h : ∀ p, W₁ p = W₂ p) : W₁ = W₂ := by
  cases W₁; cases W₂; congr; funext p; exact h p

/-- Evaluate a graphon on an unordered pair of vertices in `Sym2 UnitInterval` as a real number. -/
def evalSym2 (W : Graphon) (e : Sym2 UnitInterval) : ℝ :=
  Sym2.lift ⟨fun u v => (W (u, v) : ℝ), fun u v => by simp [W.symmetric]⟩ e

/-- Given a configuration `x : V → UnitInterval` and an edge `e : Sym2 V`, evaluate `W` on the endpoints as a real number. -/
def evalEdge {V : Type*} (W : Graphon) (x : V → UnitInterval) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => (W (x u, x v) : ℝ), fun u v => by simp [W.symmetric]⟩ e

end Graphon

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The integrand for the homomorphism density $t(H, W)$ of a simple graph $H$ in a graphon $W$
given a configuration `x : V → [0, 1]`.
-/
def graphonHomIntegrand (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) (x : V → UnitInterval) : ℝ :=
  ∏ e ∈ H.edgeFinset, W.evalEdge x e

/--
The **homomorphism density** $t(H, W)$ of a finite simple graph $H$ in a graphon $W$
on $[0, 1]$ equipped with the Lebesgue measure `volume`.
-/
noncomputable def graphonHomDensity (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) : ℝ :=
  ∫ x : V → UnitInterval, graphonHomIntegrand H W x ∂(Measure.pi fun _ => volume)

/--
The **edge density** of a graphon $W$ on $[0, 1]^2 \to [0, 1]$ equipped with the Lebesgue measure `volume`.
-/
noncomputable def graphonEdgeDensity (W : Graphon) : ℝ :=
  ∫ p : UnitInterval × UnitInterval, (W p : ℝ) ∂(volume.prod volume)

variable {V W : Type*}

/--
**Case: `H = C_{2k}` is an even cycle (Sidorenko 1993, graphon version).**

Every even cycle $C_{2k}$ satisfies Sidorenko's inequality for all graphons on $[0, 1]$.

*Reference:*
* A. Sidorenko, "A correlation inequality for bipartite graphs", Graphs Combin. 9 (1993), 201-204.
-/
theorem sidorenko_even_cycle_graphon (k : ℕ) (hk : 1 ≤ k)
    (W : Graphon) :
    (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W := by
  sorry
