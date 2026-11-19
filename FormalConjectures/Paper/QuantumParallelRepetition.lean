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
# Quantum parallel repetition for two-player one-round games

A finite two-player one-round game is given by finite question sets $X, Y$, finite answer sets
$A, B$, a probability distribution $\mu$ on $X \times Y$ and a predicate
$V : X \times Y \times A \times B \to \{0, 1\}$. In the $n$-fold parallel repetition $G^{\otimes n}$
the referee samples $n$ independent question pairs and the players win if they win every
coordinate. The entangled value $\omega^*(G)$ is the supremum of the winning probability over
finite-dimensional shared states and local measurements.

The quantum analogue of Raz's parallel repetition theorem [Raz98] asks whether
$\omega^*(G) < 1$ implies that $\omega^*(G^{\otimes n})$ decays exponentially in $n$. It was noted
as open in [CHTW04, footnote 2]. Yuen [Yue16] proved polynomial decay for all games, and
exponential decay was known for several classes of games (XOR, unique, projection and free
games). [OpenAI26, Chapter 6] proves exponential decay for every finite game.

*References:*
- [CHTW04] Cleve, R., Høyer, P., Toner, B. and Watrous, J., *Consequences and limits of nonlocal
  strategies*. Proc. 19th IEEE Conference on Computational Complexity (2004), 236-249.
  [arXiv:quant-ph/0404076](https://arxiv.org/abs/quant-ph/0404076)
- [Raz98] Raz, R., *A parallel repetition theorem*. SIAM J. Comput. 27 (1998), 763-803.
- [Yue16] Yuen, H., *A parallel repetition theorem for all entangled games*. ICALP 2016.
  [arXiv:1604.04340](https://arxiv.org/abs/1604.04340)
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science* (2026),
  Chapter 6. [PDF](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
-/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open Matrix
open scoped Kronecker ComplexOrder

/--
A finite two-player one-round game with question sets `X`, `Y` and answer sets `A`, `B`.
The referee samples questions `(x, y)` with probability `questionWeight x y`, and the players win
on answers `(a, b)` when `predicate x y a b = true`.
-/
structure Game (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : ∑ x, ∑ y, questionWeight x y = 1
  predicate : X → Y → A → B → Bool

namespace Game

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The `n`-fold parallel repetition of `G`: the `n` question pairs are sampled independently from
the distribution of `G`, and the players win if they win in every coordinate.
-/
def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys := Finset.prod_nonneg fun i _ ↦ G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc ∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∏ i, G.questionWeight (xs i) (ys i)
        = ∑ xs : Fin n → X, ∏ i, ∑ y, G.questionWeight (xs i) y :=
          Finset.sum_congr rfl fun xs _ ↦
            (Fintype.prod_sum fun i y ↦ G.questionWeight (xs i) y).symm
      _ = ∏ _i : Fin n, ∑ x, ∑ y, G.questionWeight x y :=
          (Fintype.prod_sum fun _ x ↦ ∑ y, G.questionWeight x y).symm
      _ = 1 := by simp [G.weight_normalized]
  predicate xs ys as bs := decide (∀ i, G.predicate (xs i) (ys i) (as i) (bs i) = true)

@[category test, AMS 68 81]
theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ) (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp [Game.repeat]

end Game

/-- A density matrix on a finite-dimensional space indexed by `d`. -/
structure DensityMatrix (d : Type*) [Fintype d] where
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

/-- A positive operator-valued measure with outcomes in `ι` on the space indexed by `d`. -/
structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : ∑ i, effect i = 1

/--
An entangled strategy for a game with questions `X`, `Y` and answers `A`, `B`: finite local
spaces indexed by `Alice` and `Bob`, a shared state on `Alice × Bob`, and for every question a
local measurement whose outcomes are the answers. A mixed shared state is allowed; by
purification this gives the same supremum as pure states.
-/
structure Strategy (X Y A B : Type*) [Fintype A] [Fintype B] where
  Alice : Type
  Bob : Type
  [alice_fintype : Fintype Alice]
  [bob_fintype : Fintype Bob]
  [alice_decidableEq : DecidableEq Alice]
  [bob_decidableEq : DecidableEq Bob]
  state : DensityMatrix (Alice × Bob)
  aliceMeasurement : X → POVM A Alice
  bobMeasurement : Y → POVM B Bob

attribute [instance] Strategy.alice_fintype Strategy.bob_fintype Strategy.alice_decidableEq
  Strategy.bob_decidableEq

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The probability $\mathrm{Tr}(\rho (E^x_a \otimes F^y_b))$ that the players answer `(a, b)` on
questions `(x, y)` when they use the strategy `S`.
-/
def Strategy.outcomeProbability (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (S.state.matrix * ((S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b)).trace.re

/-- The probability that the strategy `S` wins the game `G`. -/
def Game.winProbability (G : Game X Y A B) (S : Strategy X Y A B) : ℝ :=
  ∑ x, ∑ y, G.questionWeight x y *
    ∑ a, ∑ b, if G.predicate x y a b then S.outcomeProbability x y a b else 0

/-- The entangled value $\omega^*(G)$: the supremum of the winning probability of `G` over all
finite-dimensional entangled strategies. -/
def Game.entangledValue (G : Game X Y A B) : ℝ :=
  ⨆ S : Strategy X Y A B, G.winProbability S

/-- A sequence `v` is bounded by `C * exp (-c * n)` for some constants `c, C > 0`. -/
def HasExponentialBound (v : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∃ C > 0, ∀ n : ℕ, v n ≤ C * Real.exp (-c * n)

@[category test, AMS 68 81]
theorem hasExponentialBound_exp_neg : HasExponentialBound fun n ↦ Real.exp (-n) :=
  ⟨1, one_pos, 1, one_pos, fun n ↦ by simp⟩

set_option linter.style.formal_proof_palomar false in
/--
**Quantum parallel repetition.** If a finite two-player one-round game $G$ has entangled value
$\omega^*(G) < 1$, then $\omega^*(G^{\otimes n}) \le C e^{-c n}$ for some constants $c, C > 0$
depending on $G$.

This was noted as open in [CHTW04, footnote 2] and proved in [OpenAI26, Theorem 1.1].
-/
@[category research solved, AMS 68 81, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70971-L70976"]
theorem quantum_parallel_repetition {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] (G : Game X Y A B) (hG : G.entangledValue < 1) :
    HasExponentialBound fun n ↦ (G.repeat n).entangledValue := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The rate in [OpenAI26, Theorem 1.1]: there is a universal constant $c > 0$ such that for every
finite game $G$ with nonempty answer sets and $\varepsilon = 1 - \omega^*(G) > 0$,
$$\omega^*(G^{\otimes n}) \le
  \exp\left(-c \frac{\varepsilon^{13}}{\varepsilon + \log(|A||B|)} n\right)$$
for every $n \ge 1$. The exponent $13$ is not claimed to be optimal.
-/
@[category research solved, AMS 68 81, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70953-L70969"]
theorem quantum_parallel_repetition.variants.rate :
    ∃ c > 0, ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
      (G : Game X Y A B), Nonempty A → Nonempty B → 0 < 1 - G.entangledValue →
      ∀ n : ℕ, 0 < n →
        (G.repeat n).entangledValue ≤
          Real.exp (-(c * ((1 - G.entangledValue) ^ 13 /
            ((1 - G.entangledValue) + Real.log (Fintype.card A * Fintype.card B)))) * n) := by
  sorry

end QuantumParallelRepetition
