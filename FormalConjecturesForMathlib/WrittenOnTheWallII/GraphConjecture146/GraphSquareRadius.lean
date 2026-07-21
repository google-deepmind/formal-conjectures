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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.GraphSquareMetric

@[expose] public section

/-!
# Radius of a graph square

For a finite connected graph, the radius of the square graph is the ceiling
of half the original radius. The proof first identifies vertex eccentricities
by applying the graph-square distance formula to finite witnesses attaining
the relevant maxima, then applies the result to centers of the two graphs.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [Nontrivial α]
variable {G : SimpleGraph α}

private lemma eccent_ne_top_of_connected (hG : G.Connected) (u : α) :
    G.eccent u ≠ ⊤ := by
  have hed : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  intro hu
  apply hed
  exact top_unique (hu ▸ (eccent_le_ediam (G := G) (u := u)))

private lemma dist_le_eccent_toNat (hG : G.Connected) (u v : α) :
    G.dist u v ≤ (G.eccent u).toNat := by
  unfold dist
  exact ENat.toNat_le_toNat
    (edist_le_eccent (G := G) (u := u) (v := v))
    (eccent_ne_top_of_connected hG u)

/-- Vertex eccentricity in the graph square is the ceiling of half the
original vertex eccentricity. -/
lemma graphSquare_eccent_toNat (hG : G.Connected) (u : α) :
    ((graphSquare G).eccent u).toNat = ((G.eccent u).toNat + 1) / 2 := by
  apply le_antisymm
  · obtain ⟨v, hv⟩ := (graphSquare G).exists_edist_eq_eccent_of_finite u
    have hsqdist : (graphSquare G).dist u v = ((graphSquare G).eccent u).toNat := by
      unfold dist
      rw [hv]
    have hform := graphSquare_dist hG u v
    have hle := dist_le_eccent_toNat hG u v
    rw [hsqdist] at hform
    omega
  · obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
    have hgdist : G.dist u v = (G.eccent u).toNat := by
      unfold dist
      rw [hv]
    have hform := graphSquare_dist hG u v
    have hle : (graphSquare G).dist u v ≤ ((graphSquare G).eccent u).toNat :=
      dist_le_eccent_toNat (G := graphSquare G) hG.graphSquare u v
    rw [hgdist] at hform
    omega

/-- The natural-valued radius of the graph square is the ceiling of half the
natural-valued radius of the original connected graph. -/
lemma graphSquare_radius_toNat (hG : G.Connected) :
    (graphSquare G).radius.toNat = (G.radius.toNat + 1) / 2 := by
  have hsG : (graphSquare G).Connected := hG.graphSquare
  apply le_antisymm
  · obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
    have hsle : (graphSquare G).radius.toNat ≤ ((graphSquare G).eccent c).toNat :=
      ENat.toNat_le_toNat
        (radius_le_eccent (G := graphSquare G) (u := c))
        (eccent_ne_top_of_connected hsG c)
    have hecc := graphSquare_eccent_toNat hG c
    have hcNat := congrArg ENat.toNat hc
    omega
  · obtain ⟨c, hc⟩ := (graphSquare G).exists_eccent_eq_radius
    have hgle : G.radius.toNat ≤ (G.eccent c).toNat :=
      ENat.toNat_le_toNat
        (radius_le_eccent (G := G) (u := c))
        (eccent_ne_top_of_connected hG c)
    have hecc := graphSquare_eccent_toNat hG c
    have hcNat := congrArg ENat.toNat hc
    omega


section Regression

variable (hG : G.Connected) (u v : α)

example (h : G.dist u v = 1) : (graphSquare G).dist u v = 1 := by
  rw [graphSquare_dist hG, h]

example (h : G.dist u v = 2) : (graphSquare G).dist u v = 1 := by
  rw [graphSquare_dist hG, h]

example (h : G.dist u v = 3) : (graphSquare G).dist u v = 2 := by
  rw [graphSquare_dist hG, h]

example (h : G.dist u v = 4) : (graphSquare G).dist u v = 2 := by
  rw [graphSquare_dist hG, h]

example (h : G.dist u v = 5) : (graphSquare G).dist u v = 3 := by
  rw [graphSquare_dist hG, h]

end Regression


end SimpleGraph
