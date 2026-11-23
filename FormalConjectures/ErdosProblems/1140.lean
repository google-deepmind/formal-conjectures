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
# Erdős Problem 1140

*References:*
- [erdosproblems.com/1140](https://www.erdosproblems.com/1140)
- [EpGi10] Epure, M. and Gica, A., *Principal quadratic real fields in connection with some
  additive problems*. Bull. Math. Soc. Sci. Math. Roumanie (N.S.) (2010), 251-259.
- [MoWi89] Mollin, R. A. and Williams, H. C., *Period four and real quadratic fields of class
  number one*. Proc. Japan Acad. Ser. A Math. Sci. (1989), 89-93.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

namespace Erdos1140

/-- $n \geq 1$ and $n - 2x^2$ is prime for all integers $x \geq 0$ with $2x^2 < n$. The value
$x = 0$ is allowed, so $n$ itself is prime, as in the known list. -/
def Erdos1140Prop (n : ℕ) : Prop :=
  0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1140Prop n) :=
  decidable_of_iff (0 < n ∧ ∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime) <| by
    unfold Erdos1140Prop
    refine and_congr_right fun _ => ⟨fun h x hx => h x ?_ hx, fun h x _ hx => h x hx⟩
    have := Nat.le_self_pow two_ne_zero x
    omega

/-- The known examples $2, 5, 7, 13, 31, 61, 181, 199$ have the property. -/
@[category test, AMS 11]
theorem known_examples :
    ∀ n ∈ ([2, 5, 7, 13, 31, 61, 181, 199] : List ℕ), Erdos1140Prop n := by
  decide +kernel

/-- Since $x = 0$ is allowed, $4$ does not have the property, although $4 - 2 \cdot 1^2 = 2$ is
prime. -/
@[category test, AMS 11]
theorem not_four : ¬ Erdos1140Prop 4 := by
  decide +kernel

/--
Do there exist infinitely many $n$ such that $n-2x^2$ is prime for all $x$ with $2x^2<n$?

The answer is no: see `erdos_1140.variants.at_most_one_exception`.
-/
@[category research solved, question, AMS 11]
theorem erdos_1140 : ¬ {n : ℕ | Erdos1140Prop n}.Infinite := by
  sorry

/--
The known such $n$ are $2,5,7,13,31,61,181,199$. It is known that these are, with at most one
exception, all such $n$. An even such $n$ must be prime (take $x = 0$), so $n = 2$. Theorem 4.1
of Epure and Gica [EpGi10] implies that the only such
$n\equiv 1\pmod{4}$ are $5,13,61,181$, and their method, coupled with a result of Mollin and
Williams [MoWi89], implies that the only such $n\equiv 3\pmod{4}$ are $7,31,199$, and at most one
other exception.
-/
@[category research solved, AMS 11]
theorem erdos_1140.variants.at_most_one_exception :
    ({n : ℕ | Erdos1140Prop n} \ {2, 5, 7, 13, 31, 61, 181, 199}).Subsingleton := by
  sorry

end Erdos1140
