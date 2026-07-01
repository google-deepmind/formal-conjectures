import Mathlib

open scoped TensorProduct

variable (V : Type*)[NormedAddCommGroup V] [InnerProductSpace ℝ V]

def TensorContraction {k l m : ℕ} (T₁ : ⨂[ℝ]^k V) (T₂ : ⨂[ℝ]^l V) (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l) (f : ℕ ⊕ ℕ → ℕ)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (hf : Set.BijOn f (Set.sumEquiv.symm ((Set.Icc 1 k \ Prod.fst '' R),
      (Set.Icc 1 l \ Prod.snd '' R))) (Set.Icc 1 m)) :
      (⨂[ℝ]^k V) →ₗ[ℝ] ⨂[ℝ]^l V →ₗ[ℝ] ⨂[ℝ]^m V :=
  sorry -- TODO!

structure TensorNetwork (α β : Type*) where
  G : Graph α β
  /-- The assignment of a (positive) integer `r v` for each edge `v`. -/
  r : α → ℕ
  hr : ∀ x, x ∈ G.vertexSet → 0 < r x
  c : β → ℕ × ℕ
  hc : ∀ (e x y), G.IsLink e x y →
    c e ∈ (Set.Icc 1 (r x) ×ˢ Set.Icc 1 (r y))
  existsAtMostOneEdge {x : α} : Set.InjOn c {e | ∃ y, G.IsLink e x y}

/-- Given a tensor network `G`, the assignement of a tensor `T_v` for each vertex.
Note: we also assigne "junk values for elements of `α` that aren't edges". -/
structure TensorMap {α β : Type*} (T : TensorNetwork α β)  where
  tensor : ∀ x : α, ⨂[ℝ]^(T.r x) V
