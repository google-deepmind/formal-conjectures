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
# Adjacency spectral radius times radius

*References:*
- [M. Aouchiche, P. Hansen, D. Stevanović, Variable neighborhood search for extremal graphs. 17. Further conjectures and results about the index, Conjecture 4.4 (2009)](https://doi.org/10.7151/dmgt.1430)
- [J. J. Gebendorfer, On the Spectral Radius–Radius Product of Connected Graphs: A Refutation and Exact Correction of an AutoGraphiX Conjecture, 7 August 2026; manuscript archive](https://github.com/user-attachments/files/33356644/Gebendorfer_AGX_Conjecture_4_4_Source.zip)

The original conjecture is transcribed in the attached manuscript; the original
journal PDF was not freshly retrieved during the intake. The fixed-radius
classification used for the correction is credited to Hansen–Stevanović.
A bag handle has q VERTICES including both endpoints, so its order is p+q-2.
-/

@[expose] public section
namespace AouchicheHansenStevanovic.SpectralRadiusRadius
open SimpleGraph

/-- Vertices along the edge-replacing path, with endpoints zero and one. -/
def handle (p q : ℕ) : List ℕ := 0 :: ((List.range (q - 2)).map (p + ·) ++ [1])

/-- K_p with edge 01 replaced by a q-vertex path. For q=2 the edge is restored. -/
def bag (p q : ℕ) : SimpleGraph (Fin (p + q - 2)) where
  Adj u v := u ≠ v ∧
    ((u.val < p ∧ v.val < p ∧ ¬ ((u.val = 0 ∧ v.val = 1) ∨
      (u.val = 1 ∧ v.val = 0))) ∨
    (u.val, v.val) ∈ (handle p q).zip (handle p q).tail ∨
    (v.val, u.val) ∈ (handle p q).zip (handle p q).tail)
  symm := ⟨by intro u v h; aesop⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

noncomputable def objective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact sSup (spectrum ℝ (G.adjMatrix ℝ)) * G.radius.toNat

/-- The printed bag candidate is not a maximizer at every connected order
n>=3. This is the adjacency spectral-radius product, not a Laplacian product. -/
@[category research solved, AMS 5 15]
theorem conjecture4_4 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    3 ≤ n → G.Connected → objective G ≤ objective (bag (n / 2 + 2) ((n + 1) / 2)) := by
  sorry

/-- An even-handle bag is strictly improved by transferring one handle vertex
to the clique, preserving order and radius. -/
@[category research solved, AMS 5 15]
theorem even_handle (p q : ℕ) (hp : 4 ≤ p) (hq : 4 ≤ q) (heven : Even q) :
    objective (bag p q) < objective (bag (p + 1) (q - 1)) := by
  sorry

/-- The corrected odd-handle bag attains the maximum at every order at least
nine, with s=floor((n+3)/4). No uniqueness claim is added. -/
@[category research solved, AMS 5 15]
theorem corrected_large_orders (n : ℕ) (hn : 9 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) :
    let s := (n + 3) / 4
    objective G ≤ objective (bag (n - 2 * s + 3) (2 * s - 1)) := by
  sorry

/-- The complete graph at order three; otherwise the complement of a perfect
matching at even order, or of P_3 plus a matching at odd order. -/
def smallMaximizer (n : ℕ) : SimpleGraph (Fin n) :=
  if n = 3 then ⊤ else (SimpleGraph.fromRel fun u v : Fin n =>
    if n % 2 = 0 then u.val / 2 = v.val / 2 else
      ((u.val < 3 ∧ v.val < 3 ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val)) ∨
        (3 ≤ u.val ∧ 3 ≤ v.val ∧ (u.val - 3) / 2 = (v.val - 3) / 2)))ᶜ

/-- The remaining corrected maximizers at orders three through eight. -/
@[category research solved, AMS 5 15]
theorem corrected_small_orders (n : ℕ) (hn : 3 ≤ n) (h8 : n ≤ 8)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    objective G ≤ objective (smallMaximizer n) := by
  sorry

end AouchicheHansenStevanovic.SpectralRadiusRadius
