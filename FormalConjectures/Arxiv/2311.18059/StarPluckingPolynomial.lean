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
# Unimodality of star plucking polynomials with delays one and two

*References:*
- [D. Ibarra, A. Landry, G. Montoya-Vega and J. H. Przytycki,
  Exploring unimodality of the plucking polynomial with delay function,
  arXiv:2311.18059v1, Conjecture 4.1](https://arxiv.org/html/2311.18059v1)
- [J. J. Gebendorfer, Unimodality of star plucking polynomials with delays
  one and two, 13 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7309)

The operational recurrence follows the displayed recurrence, examples and
Proposition 2.5. The isolated zero-initial-condition phrase in Definition 1.7
is ambiguous. This records the identified arXiv version, not a distinct final
published chapter. The linked certificate proves all star sizes.
-/

@[expose] public section

namespace Arxiv.«2311.18059»

/-- Delayed star plucking: eligible leaves have delay one; indices run right to left.
Removing a leaf preserves order and lowers surviving delays by one, with minimum one.
The empty star has value one and a nonempty star with no eligible leaf has value zero. -/
noncomputable def starPluckingPolynomial : (n : ℕ) → (Fin n → ℕ) → Polynomial ℤ
  | 0, _ => 1
  | n+1, f => ∑ i : Fin (n+1), if f i = 1 then
      Polynomial.X ^ i.val * starPluckingPolynomial n (fun k => max 1 (f (i.succAbove k)-1)) else 0

/-- The coefficient sequence has a weakly increasing then weakly decreasing peak. -/
def IsUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

/--
Conjecture 4.1 of arXiv:2311.18059v1: every plane rooted star whose initial
leaf delays are one or two has a unimodal plucking polynomial, for every
arrangement of the delays. The recurrence represents the star by its ordered
leaves; $i$ is the number of surviving leaves to the right of the selected leaf.
Weak inequalities allow plateaus and the zero polynomial. The optional empty
star is included with value one.
-/
@[category research solved, AMS 5 57, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/b45f7e0f6a05c2a8a483ee9695cba9de04730a3a/Proofs/PluckingStarProof.lean"]
theorem conjecture4_1 : ∀ n : ℕ, ∀ f : Fin n → ℕ,
    (∀ i, f i = 1 ∨ f i = 2) → IsUnimodal (starPluckingPolynomial n f) := by
  sorry

end Arxiv.«2311.18059»
