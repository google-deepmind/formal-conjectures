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


public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

/-!
# Homomorphism density for finite simple graphs

Mathlib does not (as of 2026-04) provide `SimpleGraph.homDensity`. We define a lightweight
version here, specialised to finite vertex types on the host `G`, and prove the basic
`homDensity H G ≤ 1` upper bound used as a sanity check in Sidorenko-style arguments.

The extension to infinite hosts uses the same formula with `Fintype.card` replaced by
measure-theoretic integrals; we do not need that generality here.
-/

namespace SimpleGraph

variable {V W : Type*}

/-- The number of graph homomorphisms `H → G`, as a natural number. For finite vertex
types this is just the cardinality of the `Hom` type. -/
noncomputable def homCount [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (H →g G)

/-- The **homomorphism density** `t(H, G)` of a simple graph `H` in a simple graph `G` with
finite vertex sets is `#Hom(H, G) / |V(G)|^{|V(H)|}`. -/
noncomputable def homDensity [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount H G : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

/-- The homomorphism density `t(H, G)` is at most `1`.

Proof outline: the underlying function of a `H →g G`-homomorphism is an element of
`V → W`, which has `|W|^|V|` elements, so `homCount H G ≤ |W|^|V|`. Divide. -/
lemma homDensity_le_one {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    homDensity H G ≤ 1 := by
  -- `homCount H G = #(H →g G) ≤ #(V → W) = |W| ^ |V|`. Divide and simplify.
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have h₁ : Fintype.card (H →g G) ≤ Fintype.card (V → W) :=
    Fintype.card_le_of_injective (fun f => (f : V → W)) DFunLike.coe_injective
  have h₂ : Fintype.card (V → W) = Fintype.card W ^ Fintype.card V := Fintype.card_fun
  have hnat : homCount H G ≤ Fintype.card W ^ Fintype.card V := by
    unfold homCount
    exact h₂ ▸ h₁
  have hle : (homCount H G : ℝ) ≤ (Fintype.card W : ℝ) ^ (Fintype.card V) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    simpa [Nat.cast_pow] using this
  have hpos : (0 : ℝ) < (Fintype.card W : ℝ) ^ (Fintype.card V) :=
    pow_pos (by exact_mod_cast hWpos) _
  rw [homDensity, div_le_one hpos]
  exact hle

end SimpleGraph
