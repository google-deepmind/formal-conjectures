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
# Sum of two squares and two central-binomial-type terms

A303639 counts the ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$ with
$a, b, c, d$ nonnegative integers, $a \le b$ and $c \le d$.

*References:*
- [A303639](https://oeis.org/A303639)
- Z.-W. Sun, ["Restricted sums of four squares"](https://arxiv.org/abs/1701.05868),
  arXiv:1701.05868 [math.NT], 2017-2018.
- Z.-W. Sun, ["Refining Lagrange's four-square theorem"](https://doi.org/10.1016/j.jnt.2016.11.008),
  *J. Number Theory* **175** (2017), 167-190.
- S. Jeong, [A303639 Counterexample Project](https://github.com/DCLXAI/a303639-counterexample),
  search, certificates and independent verifiers,
  [DOI 10.5281/zenodo.21863025](https://doi.org/10.5281/zenodo.21863025). The counterexample is
  recorded as an approved comment on the OEIS entry (Aug 10 2026).
-/

namespace OeisA303639

/-- The predicate that $n$ can be written as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$
for nonnegative integers $a, b, c, d$.

This drops the normalisations $a \le b$ and $c \le d$. They do not affect whether the count is
positive, and refuting the unordered statement is the stronger result, since a representation
with $a \le b$ and $c \le d$ is in particular a representation. -/
def A (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d

@[category test, AMS 11]
theorem a_1 : ¬ A 1 := by
  rintro ⟨a, b, c, d, h⟩
  have hc : 0 < (2 * c + 1).choose c := Nat.choose_pos (by omega)
  have hd : 0 < (2 * d + 1).choose d := Nat.choose_pos (by omega)
  omega

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨0, 0, 0, 1, by decide⟩

@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨1, 0, 0, 1, by decide⟩

@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨2, 0, 0, 0, by decide⟩

/--
**Zhi-Wei Sun's Conjecture (A303639)**: any integer $n > 1$ can be written as
$a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$ with $a, b, c, d$ nonnegative integers.
Sun checked this for $n$ up to $6 \cdot 10^8$.

This is false: $n = 800322180$ admits no such representation, so $a(800322180) = 0$. Since
$\binom{33}{16} > 800322180$, only $c, d \le 15$ are possible, and each of the resulting $136$
remainders $800322180 - \binom{2c+1}{c} - \binom{2d+1}{d}$ is divisible by some prime
$p \equiv 3 \pmod 4$ to an odd power, hence is not a sum of two squares by Fermat's two-square
theorem.

The counterexample is recorded as an approved comment on the OEIS entry; the Lean proof linked
below formalises this argument, and was produced by Claude Opus 5 prompted by Sunsu Jeong
([DCLXAI](https://github.com/DCLXAI)).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/DCLXAI/a303639-counterexample/blob/8e21c57c622b05a1815bcf9927458ebb3973ef2e/lean/A303639/Counterexample.lean"]
theorem conjecture : ¬ ∀ n : ℕ, 1 < n → A n := by
  sorry

/-- The counterexample witnessing that A303639 vanishes: $a(800322180) = 0$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/DCLXAI/a303639-counterexample/blob/8e21c57c622b05a1815bcf9927458ebb3973ef2e/lean/A303639/Counterexample.lean"]
theorem conjecture.counterexample : ¬ A 800322180 := by
  sorry

end OeisA303639
