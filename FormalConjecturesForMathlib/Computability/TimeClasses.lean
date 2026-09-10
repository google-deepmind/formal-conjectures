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

public import FormalConjecturesForMathlib.Computability.Complexity
public import Mathlib.Data.Nat.Basic

/-!
# Exponential-time classes on the existing TM2 model

EXP uses an exponential bound in encoded input length. NEXP uses exponential
certificates and a deterministic TM2 verifier whose running time, on eligible
certificates, is exponential in the original input length, not certificate length.

References: Arora–Barak, author draft dated 2007-01-08, Definition 2.24 (§2.6.2),
and the certificate characterization in the proof of Lemma 16.26:
https://theory.cs.princeton.edu/complexity/book.pdf.
-/

@[expose] public section

namespace ComplexityTheory

/-- Computation with an arbitrary time bound in the encoded input length. -/
def IsTimeBound {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (t : ℕ → ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableInTime BitstringEncoding.bitEncode
    BitstringEncoding.bitEncode f, ∀ n, M.time n ≤ t n

theorem IsTimeBound.mono {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} {s t : ℕ → ℕ} (h : IsTimeBound f s)
    (hst : ∀ n, s n ≤ t n) : IsTimeBound f t := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun n => (hM n).trans (hst n)⟩

/-- Exponential time means a bound 2 to a fixed natural-coefficient polynomial. -/
def IsExpTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : Prop :=
  ∃ p : Polynomial ℕ, IsTimeBound f (fun n => 2 ^ p.eval n)

theorem IsPolyTime.isExpTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (h : IsPolyTime f) : IsExpTime f := by
  obtain ⟨M⟩ := h
  exact ⟨M.time, M.toTM2ComputableInTime, fun n => (Nat.lt_two_pow_self).le⟩

/-- Deterministic exponential time on bitstrings. -/
def EXP : Set DecisionProblem := {L | IsExpTime L}

theorem P_subset_EXP : P ⊆ EXP :=
  fun _ h => IsPolyTime.isExpTime h

/-- A single finite TM2 verifies every eligible input-certificate pair within a
bound depending only on the original input. There is no requirement outside
the indicated certificate-length bound. -/
def HasExponentialVerifier (p q : Polynomial ℕ)
    (R : (List Bool × List Bool) → Bool) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ x w : List Bool,
    w.length ≤ 2 ^ p.eval x.length →
      Nonempty (Turing.TM2OutputsInTime M.tm
        ((BitstringEncoding.bitEncode (x, w)).map M.inputAlphabet.invFun)
        (some ((BitstringEncoding.bitEncode (R (x, w))).map M.outputAlphabet.invFun))
        (2 ^ q.eval x.length))

/-- Nondeterministic exponential time, via bounded certificates and a verifier
clocked exponentially in the original input length. Both polynomials and the
verifier are fixed before the input is quantified. -/
def NEXP : Set DecisionProblem :=
  {L | ∃ (p q : Polynomial ℕ) (R : (List Bool × List Bool) → Bool),
    HasExponentialVerifier p q R ∧
    ∀ x, L x = true ↔
      ∃ w : List Bool, w.length ≤ 2 ^ p.eval x.length ∧ R (x, w) = true}

/-- Expanding the time exponent pointwise preserves the verifier guarantee. -/
theorem HasExponentialVerifier.mono {p q r : Polynomial ℕ}
    {R : (List Bool × List Bool) → Bool} (h : HasExponentialVerifier p q R)
    (hqr : ∀ n, q.eval n ≤ r.eval n) : HasExponentialVerifier p r R := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun x w hw => ?_⟩
  obtain ⟨hRun⟩ := hM x w hw
  exact ⟨⟨hRun.toEvalsTo,
    hRun.steps_le_m.trans (Nat.pow_le_pow_right (by decide) (hqr x.length))⟩⟩

end ComplexityTheory
