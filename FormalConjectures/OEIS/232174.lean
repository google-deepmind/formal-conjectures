/-
Copyright 2025 The Formal Conjectures Authors.

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
# Representations with prime conditions

Any integer $n > 1$ can be written as $x + y$ with $x, y > 0$ such that both $x + ny$ and
$x^2 + ny^2$ are prime.

Zhi-Wei Sun has offered a $200 prize for the first proof.

*References:*
- [OEIS A232174](https://oeis.org/A232174)
- Z.-W. Sun, "Conjectures on representations involving primes," in: M. Nathanson (ed.),
  Combinatorial and Additive Number Theory II: CANT, Springer Proc. in Math. & Stat.,
  Vol. 220, Springer, 2017, pp. 279-310. https://arxiv.org/abs/1211.1588
- D.A. Cox, "Primes of the Form x² + ny²," John Wiley & Sons, 1989.
-/

namespace OeisA232174

/-- The predicate that `n` can be written as $x + y$ with $x, y > 0$ such that both
$x + ny$ and $x^2 + ny^2$ are prime. -/
def HasPrimeRepresentation (n : ℕ) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ (x + n * y).Prime ∧ (x ^ 2 + n * y ^ 2).Prime

@[category test, AMS 11]
theorem hasPrimeRepresentation_2 : HasPrimeRepresentation 2 :=
  ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem hasPrimeRepresentation_5 : HasPrimeRepresentation 5 :=
  ⟨3, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem hasPrimeRepresentation_8 : HasPrimeRepresentation 8 :=
  ⟨5, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/--
**Zhi-Wei Sun's Conjecture (A232174)**: Any integer $n > 1$ can be written as $x + y$ with
$x, y > 0$ such that both $x + ny$ and $x^2 + ny^2$ are prime.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : HasPrimeRepresentation n := by
  sorry

end OeisA232174
