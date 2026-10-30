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
# Byzov–Pushkarev automorphisms of the block-circulant DSRG family

*References:*
- [V. A. Byzov and I. A. Pushkarev, version 2, Equation (17), Theorem 7 and Conjecture 8](https://arxiv.org/html/2603.07707v2)
- [J. J. Gebendorfer, The Automorphism Group of the Byzov–Pushkarev Directed Strongly Regular Graph Family, 24 July 2026; manuscript archive](https://github.com/user-attachments/files/33368206/Byzov_Intake_Gebendorfer_2026-10-13.zip)

The domain is the formula-defined sequence, not every DSRG with those parameters.
Exponent sets encode the exact circulant convention (i,z) -> (j,z+r). The binary
augmentation group has sum of coordinates zero and is acted on by cyclic shift.
-/

@[expose] public section
namespace ByzovPushkarev
open Finset

abbrev orderParameter (n : ℕ) : ℕ := 2 * n + 3
instance (n : ℕ) : NeZero (orderParameter n) := ⟨by dsimp [orderParameter]; omega⟩

abbrev Coord (n : ℕ) := ZMod (orderParameter n)
abbrev Vertex (n : ℕ) := Fin 9 × Coord n

def shiftSet {n : ℕ} (a : Coord n) (E : Finset (Coord n)) : Finset (Coord n) :=
  E.image (fun r => r + a)

def pSet (n : ℕ) : Finset (Coord n) := (range (n + 1)).image fun (i : ℕ) => (i : Coord n)
def rSet (n : ℕ) : Finset (Coord n) := univ \ {((n - 1 : ℕ) : Coord n), ((2 * n + 1 : ℕ) : Coord n)}
def sSet (n : ℕ) : Finset (Coord n) := univ \ {0, 2, ((n + 2 : ℕ) : Coord n), ((n + 3 : ℕ) : Coord n)}

def rowA (n : ℕ) : Fin 9 → Finset (Coord n) :=
  ![∅, pSet n, shiftSet 1 (pSet n), shiftSet ((n - 1 : ℕ) : Coord n) (pSet n),
    shiftSet ((n - 2 : ℕ) : Coord n) (pSet n), {((2 * n : ℕ) : Coord n)}, {1, ((n + 1 : ℕ) : Coord n)},
    shiftSet 2 (pSet n), shiftSet 1 (pSet n)]

def rowB (n : ℕ) : Fin 9 → Finset (Coord n) :=
  ![univ, {0}, {1}, {((n - 1 : ℕ) : Coord n)}, {((n - 2 : ℕ) : Coord n)}, rSet n, sSet n, {2}, {1}]

/-- Adjacency of the actual nine-by-nine circulant-block construction. -/
def adjacent (n : ℕ) (u v : Vertex n) : Prop :=
  v.2 - u.2 ∈ if u.1.val < 6 then shiftSet (u.1.val : Coord n) (rowA n v.1)
    else rowB n v.1

/-- The augmentation subgroup of the binary coordinate group. -/
noncomputable def augmentation (m : ℕ) [NeZero m] : AddSubgroup (ZMod m → ZMod 2) where
  carrier := {f | ∑ i : ZMod m, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∑ i, f i) = 0 at hf
    change (∑ i, g i) = 0 at hg
    change (∑ i, (f i + g i)) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  neg_mem' := by
    intro f hf
    change (∑ i, f i) = 0 at hf
    change (∑ i, -f i) = 0
    rw [Finset.sum_neg_distrib, hf, neg_zero]

noncomputable def shiftAugmentation {m : ℕ} [NeZero m] (a : ZMod m) :
    augmentation m ≃+ augmentation m where
  toFun f := ⟨fun i => f.val (i + a), by
    change (∑ i : ZMod m, f.val (i + a)) = 0
    have h := Equiv.sum_comp (Equiv.addRight a) f.val
    change (∑ i : ZMod m, f.val (i + a)) = ∑ i : ZMod m, f.val i at h
    exact h.trans f.property⟩
  invFun f := ⟨fun i => f.val (i - a), by
    change (∑ i : ZMod m, f.val (i - a)) = 0
    have h := Equiv.sum_comp (Equiv.addRight (-a)) f.val
    change (∑ i : ZMod m, f.val (i + -a)) = ∑ i : ZMod m, f.val i at h
    simpa only [sub_eq_add_neg] using h.trans f.property⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := rfl

noncomputable def cyclicAction (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →* MulAut (Multiplicative (augmentation m)) where
  toFun a := AddEquiv.toMultiplicative (shiftAugmentation a.toAdd)
  map_one' := by
    ext f i
    change f.toAdd.val (i + 0) = f.toAdd.val i
    simp
  map_mul' a b := by
    ext f i
    change f.toAdd.val (i + (a.toAdd + b.toAdd)) =
      f.toAdd.val ((i + a.toAdd) + b.toAdd)
    rw [add_assoc]

/-- For n>=2 and m=2n+3, the automorphism group of D_n is
$C_2\times(C_2^{m-1}\rtimes C_m)$, with the cyclic shift acting on the binary
augmentation subgroup. RelIso supplies the actual relation-automorphism group. -/
@[category research solved, AMS 5 20, formal_proof using lean4 at
  "https://github.com/RhudeJJJJ/formal-conjectures/blob/a0a4a998ac81abeb7af3105046be608594db721b/Proofs/Byzov/Full.lean#L15"]
theorem conjecture8 (n : ℕ) (hn : 2 ≤ n) :
    Nonempty ((RelIso (adjacent n) (adjacent n)) ≃*
      (Multiplicative (ZMod 2) ×
        SemidirectProduct (Multiplicative (augmentation (orderParameter n)))
          (Multiplicative (Coord n)) (cyclicAction (orderParameter n)))) := by
  sorry

end ByzovPushkarev
