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
# Number of different products of subsets of $\{1, 2, \dots, n\}$

The number of distinct products (including the empty product 1) of any subset
of $\{1, 2, \dots, n\}$.

*References:*
- [A060957](https://oeis.org/A060957)
- [Li26] Wentao Li, [A counterexample to the A060957 interpolation conjecture](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/3be119e75ba5b31f034dc0c0b249975d17def711/proofs/new-proofs/A060957/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA60957

/-- Number of different products of any subset of $\{1, 2, \dots, n\}$. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.image (·.prod id)).card

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 2 := by
  decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 4 := by
  decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 8 := by
  decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 16 := by
  decide

/-- The set of products of subsets of $\{1, \dots, n\}$. -/
def productsOfSubsets (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ s ⊆ Finset.Icc 1 n, m = s.prod id}

namespace Counterexample

/-- The distinguished prime in the explicit circuit candidate. -/
def circuitPrime : ℕ := 9304595970494411110326649421962412033

/-- Auxiliary diagonal primes, arranged in six rows and twelve columns. -/
def circuitDiag : Fin 6 → Fin 12 → ℕ := ![
  ![199, 13381, 10369, 8761, 6991, 6427, 5623, 5323, 4861, 4327, 4177, 3821],
  ![4099, 65537, 65539, 65543, 65551, 65557, 65563, 65579, 65581, 65587, 65599, 65609],
  ![4111, 65617, 65629, 65633, 65647, 65651, 65657, 65677, 65687, 65699, 65701, 65707],
  ![4127, 65713, 65717, 65719, 65729, 65731, 65761, 65777, 65789, 65809, 65827, 65831],
  ![4129, 65837, 65839, 65843, 65851, 65867, 65881, 65899, 65921, 65927, 65929, 65951],
  ![4133, 65957, 65963, 65981, 65983, 65993, 66029, 66037, 66041, 66047, 66067, 66071]]

/-- Auxiliary primes for the eleven cross coordinates. -/
def circuitCross : Fin 11 → ℕ := ![3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- The coordinates of the circuit cone. -/
abbrev CircuitCoord := (Fin 6 × Fin 12) ⊕ Fin 11

/-- The auxiliary prime belonging to a coordinate. -/
def circuitAux : CircuitCoord → ℕ
  | .inl ij => circuitDiag ij.1 ij.2
  | .inr j => circuitCross j

/-- All primes used in the construction, with the distinguished prime at none. -/
def circuitBasis : Option CircuitCoord → ℕ
  | none => circuitPrime
  | some q => circuitAux q

/-- A monomial in an indexed family of primes. -/
def primeMonomial {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℕ) : ℕ :=
  ∏ i, q i ^ e i

/-- The original-domain initial-segment endpoint. -/
irreducible_def circuitN : ℕ := circuitPrime * 2 ^ 189

/-- All auxiliary coordinates have multiplicity two in the target core. -/
def circuitCoreExp : Option CircuitCoord → ℕ
  | none => 0
  | some _ => 2

/-- The common p-free core of the two circuit profiles. -/
irreducible_def circuitCore : ℕ := primeMonomial circuitBasis circuitCoreExp

/-- Balanced-base combination of finitely many additive weights. -/
def combinedWeight (B : ℤ) : List (ℕ → ℤ) → ℕ → ℤ
  | [], _ => 0
  | w :: ws, x => w x + B * combinedWeight B ws x

/-- The rectangle constraints defining the circuit subspace. -/
def circuitRectWeight (i : Fin 5) (j : Fin 11) (x : ℕ) : ℤ :=
    (x.factorization (circuitDiag i.succ j.succ) : ℤ) -
    x.factorization (circuitDiag i.succ 0) - x.factorization (circuitDiag 0 j.succ) +
    x.factorization (circuitDiag 0 0)

/-- The parity constraints make the circuit normal form integral. -/
def circuitCrossWeight (j : Fin 11) (x : ℕ) : ℤ :=
    2 * (x.factorization (circuitCross j) : ℤ) -
    x.factorization (circuitDiag 0 0) - x.factorization (circuitDiag 0 j.succ)

/-- All sixty-six defining constraints, in a fixed order. -/
def circuitWeights : List (ℕ → ℤ) :=
    ((List.finRange 5).flatMap fun i => (List.finRange 11).map (circuitRectWeight i)) ++
    (List.finRange 11).map circuitCrossWeight

/-- A sufficiently large base prevents cancellation between constraint digits. -/
def circuitWeightBase : ℤ := 4 * (circuitN : ℤ) + 1

/-- The additive weight exposing the circuit face of the original domain. -/
def circuitWeight : ℕ → ℤ := combinedWeight circuitWeightBase circuitWeights

/-- The positive-weight factors are forced in every endpoint representation. -/
irreducible_def circuitPositive : Finset ℕ :=
  (Finset.Icc 1 circuitN).filter (fun x => 0 < circuitWeight x)

/-- The explicit common multiplier obtained from the supporting face. -/
@[irreducible] def circuitMultiplier : ℕ := circuitPositive.prod id

/-- The lower endpoint parameter in the exact counterexample. -/
@[irreducible] def circuitM : ℕ := circuitMultiplier * circuitCore

end Counterexample

/--
An explicit counterexample from [Li26]: both endpoint products occur, but the intermediate
product with exponent $5$ does not. The definitions above specify every parameter, including
`Counterexample.circuitM` as a finite product.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/3be119e75ba5b31f034dc0c0b249975d17def711/LeanOeisProofs/NewProofs/A060957.lean#L1479"]
theorem counterexample :
    Counterexample.circuitPrime.Prime ∧ Counterexample.circuitPrime ≤ Counterexample.circuitN ∧
    Counterexample.circuitM ∈ productsOfSubsets Counterexample.circuitN ∧
    Counterexample.circuitPrime ^ 6 * Counterexample.circuitM ∈
      productsOfSubsets Counterexample.circuitN ∧
    0 < (5 : ℕ) ∧ 5 < (6 : ℕ) ∧
    Counterexample.circuitPrime ^ 5 * Counterexample.circuitM ∉
      productsOfSubsets Counterexample.circuitN := by
  sorry

/--
Conjecture: let $p \le n$ be prime. If $m$ and $p^a m$ are two such products, then so is $p^k m$
for all $0 < k < a$.
- Yan Sheng Ang, Feb 13 2020

Disproved by Wentao Li (2026), with AI assistance; see [Li26]. The counterexample has
$p = 7 \cdot 2^{120} + 1$, $n = p \cdot 2^{189}$, $a = 6$, and $k = 5$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/3be119e75ba5b31f034dc0c0b249975d17def711/LeanOeisProofs/NewProofs/A060957.lean#L1499"]
theorem conjecture :
    ¬ ∀ (n p : ℕ), p.Prime → p ≤ n →
      ∀ (m a_exp : ℕ), m ∈ productsOfSubsets n → p ^ a_exp * m ∈ productsOfSubsets n →
        ∀ k : ℕ, 0 < k → k < a_exp → p ^ k * m ∈ productsOfSubsets n := by
  sorry

end OeisA60957
