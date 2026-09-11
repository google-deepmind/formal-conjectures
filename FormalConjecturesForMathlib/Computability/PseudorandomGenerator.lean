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

public import FormalConjecturesForMathlib.Computability.BooleanCircuit
public import FormalConjecturesForMathlib.Computability.RandomizedAlgorithms
public import Mathlib.Data.Nat.Log

/-!
# Uniform pseudorandom generators against Boolean circuits

The distinguishers are general De Morgan circuits, with unrestricted sharing and
free NOT gates and inputs; size counts binary AND/OR gates. This is exactly the
size convention in Vadhan, *Pseudorandomness*, §7.1.1, p. 214. The generator
definitions follow Definitions 7.3, 7.4 and 7.7 and the logarithmic-seed regime
on p. 218:
https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.

Uniformity includes an algorithm computing the seed length. Output length is
supplied in unary, so polynomial time is measured in the output length, not its
logarithm. Stretch and security are required eventually, avoiding impossible
small-length requirements such as a stretching generator for zero output bits.
-/

@[expose] public section

namespace ComplexityTheory

open BooleanCircuit BooleanTruthTable

/-- Evaluate a typed circuit on a list; length is constrained separately. -/
def circuitTest {m : ℕ} (C : Circuit (Fin m)) (bits : List Bool) : Bool :=
  C.eval (fun i => bits[i.val]?.getD false)

@[simp]
theorem circuitTest_ofFn {m : ℕ} (C : Circuit (Fin m)) (v : Fin m → Bool) :
    circuitTest C (List.ofFn v) = C.eval v := by
  unfold circuitTest
  congr 1
  funext i
  simp

/-- A finite generator stretches its seed and fools every circuit of the given size. -/
def IsPRG (d m size : ℕ) (ε : ℚ) (G : List Bool → List Bool) : Prop :=
  d < m ∧
  (∀ r, r.length = d → (G r).length = m) ∧
  ∀ C : Circuit (Fin m), C.size ≤ size →
    |RandomCoins.probability d (fun r => circuitTest C (G r)) -
      RandomCoins.probability m (circuitTest C)| ≤ ε

/-- One uniform algorithm computes the seed length; another computes every output. -/
def UniformPolyTimeGenerator (d : UnarySize → ℕ)
    (G : UnarySize × List Bool → List Bool) : Prop :=
  IsPolyTime d ∧ IsPolyTime G ∧
    ∀ m r, r.length = d m → (G (m, r)).length = m.value

/-- The logarithmic-seed, constant-error derandomization target of Vadhan §7.1.2.
This is not cryptographic polynomial time in the seed length. -/
def LogSeedPRGExists : Prop :=
  ∃ (d : UnarySize → ℕ) (G : UnarySize × List Bool → List Bool),
    UniformPolyTimeGenerator d G ∧
    ∃ c m₀ : ℕ, 0 < c ∧ 2 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m →
        d ⟨m⟩ ≤ c * Nat.log2 m ∧
        IsPRG (d ⟨m⟩) m m (1 / 8) (fun r => G (⟨m⟩, r))

theorem isPRG_size_mono {d m s t : ℕ} {ε : ℚ} {G : List Bool → List Bool}
    (h : IsPRG d m s ε G) (ht : t ≤ s) : IsPRG d m t ε G :=
  ⟨h.1, h.2.1, fun C hc => h.2.2 C (hc.trans ht)⟩

theorem isPRG_error_mono {d m s : ℕ} {ε δ : ℚ} {G : List Bool → List Bool}
    (h : IsPRG d m s ε G) (hε : ε ≤ δ) : IsPRG d m s δ G :=
  ⟨h.1, h.2.1, fun C hc => (h.2.2 C hc).trans hε⟩

theorem not_isPRG_zero_output (d size : ℕ) (ε : ℚ) (G : List Bool → List Bool) :
    ¬ IsPRG d 0 size ε G := fun h => Nat.not_lt_zero _ h.1

end ComplexityTheory
