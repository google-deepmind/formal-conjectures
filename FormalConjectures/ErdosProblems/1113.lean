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
# Erdős Problem 1113

Are there Sierpiński numbers for which no finite covering set of primes exists?

*Reference:* [erdosproblems.com/1113](https://www.erdosproblems.com/1113)

*Related problems:* #203, #276

*OEIS:* [A076336](https://oeis.org/A076336)

[Si60] Sierpiński, W., _Sur un problème concernant les nombres k·2ⁿ+1_. Elem. Math. **15**
(1960), 73–74.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Iz95] Izotov, A., _A note on Sierpinski numbers_. Fibonacci Quart. **33** (1995), 206–207.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), xviii+437.

[FFK08] Filaseta, M., Finch, C., and Kozek, M., _On powers associated with Sierpiński numbers,
Riesel numbers, and Polignac's conjecture_. J. Number Theory **128** (2008), 1916–1940.
-/

namespace Erdos1113

/-- A positive odd integer $m$ is a *Sierpiński number* if $2^k \cdot m + 1$ is composite
for all $k \geq 0$. -/
def IsSierpinskiNumber (m : ℕ) : Prop :=
  0 < m ∧ ¬ 2 ∣ m ∧ ∀ k : ℕ, ¬ Nat.Prime (2 ^ k * m + 1)

/-- A finite set of primes $P$ is a *covering set* for $m$ if every $2^k \cdot m + 1$ is
divisible by some prime $p \in P$. -/
def HasFiniteCoveringSet (m : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧ ∀ k : ℕ, ∃ p ∈ P, p ∣ (2 ^ k * m + 1)

/--
Are there Sierpiński numbers with no finite covering set of primes? [ErGr80, p.27]

Erdős and Graham conjectured the answer is yes, since otherwise this would imply there
are infinitely many Fermat primes. Izotov [Iz95] proved that $m = 734110615000775^4$ is
a Sierpiński number, and Filaseta, Finch, and Kozek [FFK08] gave a detailed argument that
it has no finite covering set.
-/
@[category research open, AMS 11]
theorem erdos_1113 : answer(sorry) ↔
    ∃ m : ℕ, IsSierpinskiNumber m ∧ ∀ P : Finset ℕ, ¬ HasFiniteCoveringSet m P := by
  sorry

/--
Filaseta, Finch, and Kozek [FFK08] conjectured that every Sierpiński number is either a
perfect power or has a finite covering set of primes. This is a refinement of the original
question: it predicts that Sierpiński numbers without covering sets exist, but only among
perfect powers.
-/
@[category research open, AMS 11]
theorem erdos_1113_variant : (∀ m : ℕ, IsSierpinskiNumber m →
    (∃ b k : ℕ, 1 < k ∧ m = b ^ k) ∨ (∃ P : Finset ℕ, HasFiniteCoveringSet m P)) := by
  sorry

end Erdos1113
