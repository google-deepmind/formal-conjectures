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
# Conjectures associated with A2897

The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.

The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.

*References:*
- [A2897](https://oeis.org/A2897)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA2897


open Polynomial

open Nat MvPolynomial

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 8 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 216 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 8000 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 343000 := by rfl


/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.

The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/2897.wip.lean#L408"]
theorem a_eq_coeff (n : ℕ) : (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by
    sorry

end OeisA2897
