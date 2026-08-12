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

import FormalConjecturesUtil

/-!
# Representation of sequence terms by harmonic numbers $\lfloor \frac{1}{2H(n) - H(n^2+n-1) - \gamma} \rfloor$

A227582: Expansion of $(2+3x+2x^2+2x^3+3x^4+x^5-x^6)/(1-2x+x^2-x^5+2x^6-x^7)$.

The sequence satisfies the linear recurrence:
$$a(n) = 2 a(n-1) - a(n-2) + a(n-5) - 2 a(n-6) + a(n-7)$$
with initial values $a(1) = 2, a(2) = 7, a(3) = 14, a(4) = 23, a(5) = 35, a(6) = 50, a(7) = 67$.

The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.

*References:*
- [A227582](https://oeis.org/A227582)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA227582


open BigOperators LinearRecurrence

/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.
-/
def baseSeq (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_zero$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
Expansion of $(2+3x+2x^2+2x^3+3x^4+x^5-x^6)/(1-2x+x^2-x^5+2x^6-x^7)$, 1-indexed.
-/
def a (n : ℕ) : ℕ :=
  if 0 < n then
    (baseSeq (n - 1)).toNat
  else
    0


@[category test, AMS 11]
lemma a_1 : a 1 = 2 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_2 : a 2 = 7 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_3 : a 3 = 14 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_4 : a 4 = 23 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_5 : a 5 = 35 := by dsimp [a]; native_decide

/--
The linear recurrence:
$$b(n + 7) = 2 b(n + 6) - b(n + 5) + b(n + 2) - 2 b(n + 1) + b(n)$$
holds for `baseSeq`. This follows directly from `LinearRecurrence.is_sol_mkSol`.
-/
@[category API, AMS 11]
theorem baseSeq_recurrence (n : ℕ) :
    baseSeq (n + 7) = 2 * baseSeq (n + 6) - baseSeq (n + 5) +
    baseSeq (n + 2) - 2 * baseSeq (n + 1) + baseSeq n := by
  let E : LinearRecurrence ℤ := ⟨7, ![1, -2, 1, 0, 0, -1, 2]⟩
  let init : Fin 7 → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  -- baseSeq is definitionally E.mkSol init
  change E.mkSol init (n + 7) =
    2 * E.mkSol init (n + 6) - E.mkSol init (n + 5) +
    E.mkSol init (n + 2) - 2 * E.mkSol init (n + 1) + E.mkSol init n
  have h := E.is_sol_mkSol init n
  -- h : mkSol(n+7) = ∑ i : Fin 7, coeffs[i] * mkSol(n+i)
  rw [h]
  -- Expand the sum and reduce all coefficient lookups
  simp only [Fin.sum_univ_seven, E, Fin.isValue]
  -- Reduce matrix lookups: ![1, -2, 1, 0, 0, -1, 2] i for all i : Fin 7
  -- and Fin coercions: ↑(i : Fin 7) for each i
  norm_num [show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 0 = 1 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 1 = -2 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 2 = 1 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 3 = 0 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 4 = 0 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 5 = -1 from rfl,
    show (![1, -2, 1, 0, 0, -1, 2] : Fin 7 → ℤ) 6 = 2 from rfl]
  ring

/--
Conjecture (from A227581): $a(n) = \lfloor 1/(2 H(n) - H(n^2 + n - 1) - \gamma) \rfloor$,
where $H$ denotes harmonic numbers and $\gamma$ denotes the Euler-Mascheroni constant.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/227582.wip.lean#L282"]
theorem a_eq_floor_harmonic_expr (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat := by
    sorry

end OeisA227582
