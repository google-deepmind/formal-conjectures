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
# Anti-unimodal delays on general plane rooted trees

*References:*
- [D. Ibarra, A. Landry, G. Montoya-Vega and J. H. Przytycki, Exploring
  unimodality of the plucking polynomial with delay function,
  arXiv:2311.18059v1, Definition 1.7 and Open Problem 4.2](https://arxiv.org/html/2311.18059v1)
- [J. J. Gebendorfer, Nonunimodal plucking polynomials with anti-unimodal
  delays, 14 October 2026](https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip)

The root is implicit and each nonroot parent is either the root or a smaller
label. Children are ordered by label. PreorderLabels ensures that increasing
leaf labels give the planar order. Every live nonroot vertex represents its
incoming edge. RightOf counts right sibling branches along the actual parent
paths, including attachment edges.

The polynomial follows the displayed delayed recurrence and examples. The
isolated zero-initial-condition phrase of Definition 1.7 is ambiguous; here an
empty eligible-leaf sum is zero. Newly exposed leaves get delay one. Fuel is
the initial number of nonroot vertices, one of which is erased at each step.
The certificate proves the exact-cardinality recurrence and polynomial
coefficient bridge. This is the general tree question, not the proved
anti-unimodal star theorem or the separate binary-delay star conjecture.
-/

@[expose] public section

namespace Arxiv.«2311.18059».GeneralPlucking

open SimpleGraph Finset

def Valid {n : ℕ} (parent : Fin n → Option (Fin n)) : Prop :=
  ∀ v w, parent v = some w → w.val < v.val

def ancestors {n : ℕ} (parent : Fin n → Option (Fin n)) : ℕ → Fin n → Finset (Fin n)
  | 0, _ => ∅
  | k+1, v => insert v (match parent v with | none => ∅ | some w => ancestors parent k w)

def PreorderLabels {n : ℕ} (p : Fin n → Option (Fin n)) : Prop :=
  ∀ a b c, a ∈ ancestors p n b → a ≤ c → c ≤ b → a ∈ ancestors p n c

def RightOf {n : ℕ} (parent : Fin n → Option (Fin n)) (x y : Fin n) : Prop :=
  ∃ a ∈ ancestors parent n x, ∃ b ∈ ancestors parent n y,
    parent a = parent b ∧ a.val < b.val

instance {n : ℕ} (p : Fin n → Option (Fin n)) (x y : Fin n) : Decidable (RightOf p x y) :=
  inferInstanceAs (Decidable (∃ a ∈ ancestors p n x, ∃ b ∈ ancestors p n y,
    p a = p b ∧ a.val < b.val))

def IsLeaf {n : ℕ} (parent : Fin n → Option (Fin n)) (live : Finset (Fin n)) (v : Fin n) : Prop :=
  v ∈ live ∧ ∀ w ∈ live, parent w ≠ some v

instance {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (v : Fin n) :
    Decidable (IsLeaf p s v) := inferInstanceAs (Decidable (v ∈ s ∧ ∀ w ∈ s, p w ≠ some v))

def eligible {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (f : Fin n → ℕ) :
    Finset (Fin n) := s.filter fun v => IsLeaf p s v ∧ f v = 1

def rightCount {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (v : Fin n) : ℕ :=
  (s.filter fun w => RightOf p v w).card

def nextDelay {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n))
    (f : Fin n → ℕ) (w : Fin n) : ℕ :=
  if IsLeaf p s w then max 1 (f w - 1) else 1

noncomputable def polynomial {n : ℕ} (p : Fin n → Option (Fin n)) :
    ℕ → Finset (Fin n) → (Fin n → ℕ) → Polynomial ℤ
  | 0, s, _ => if s = ∅ then 1 else 0
  | k+1, s, f => if s = ∅ then 1 else
      ∑ v ∈ eligible p s f, Polynomial.X ^ rightCount p s v *
        polynomial p k (s.erase v) (nextDelay p s f)

def PolynomialUnimodal (P : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → P.coeff i ≤ P.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → P.coeff j ≤ P.coeff i)

def AntiUnimodal {m : ℕ} (a : Fin m → ℕ) : Prop :=
  ∃ t : Fin m, (∀ i j, i ≤ j → j ≤ t → a j ≤ a i) ∧
    (∀ i j, t ≤ i → i ≤ j → a i ≤ a j)

/--
Open Problem 4.2 of arXiv:2311.18059v1 asks whether every plane rooted tree
with an anti-unimodal delay function has a unimodal plucking polynomial.
Anti-unimodality uses weak inequalities and allows an endpoint minimum.
The ordered nonroot parent representation below has a unique root path and
no cycles because parents have smaller labels. An eight-edge witness has
initial leaf delays $(1,1,2,3)$ and consecutive coefficients $9,8,9$ at degrees
ten, eleven and twelve, giving the negative answer. The empty polynomial is
unimodal under the stated weak-peak convention.
-/
@[category research solved, AMS 5 57, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/66d81217cd33c8c37a3b1846289423ccff5c9ba4/Proofs/PluckingAntiUnimodalAudit.lean"]
theorem open_problem4_2 : answer(False) ↔
    ∀ (n : ℕ) (p : Fin n → Option (Fin n)), Valid p → PreorderLabels p →
      ∀ f : Fin n → ℕ, (∀ v, 0 < f v) →
      ∀ (m : ℕ) (order : Fin m → Fin n), StrictMono order →
        Finset.univ.image order = Finset.univ.filter (IsLeaf p Finset.univ) →
        AntiUnimodal (f ∘ order) → PolynomialUnimodal (polynomial p n Finset.univ f) := by
  sorry

end Arxiv.«2311.18059».GeneralPlucking
