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

import FormalConjectures.Util.ProblemImports

/-!
# Conjectures associated with A227582

The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.

A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
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
def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_zero$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0


@[category test, AMS 11]
lemma a_two : a 2 = 7 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_three : a 3 = 14 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_four : a 4 = 23 := by dsimp [a]; native_decide

@[category test, AMS 11]
lemma a_five : a 5 = 35 := by dsimp [a]; native_decide


/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.

A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/227582.wip.lean#L282"]
theorem a_eq_floor_harmonic_expr (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat := by
    sorry

end OeisA227582
