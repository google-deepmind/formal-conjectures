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
# Erdős Problem 892

*Reference:* [erdosproblems.com/892](https://www.erdosproblems.com/892)

Is there a necessary and sufficient condition for a sequence of integers
$b_1 < b_2 < \cdots$ that ensures there exists a primitive sequence
$a_1 < a_2 < \cdots$ (i.e. no element divides another) with $a_n \ll b_n$
for all $n$?

Erdős [Er35] proved the necessary condition $\sum \frac{1}{b_n \log b_n} < \infty$,
and Erdős, Sárközy, and Szemerédi [ESS67] proved the necessary condition
$\sum_{b_n < x} \frac{1}{b_n} = o\!\left(\frac{\log x}{\sqrt{\log\log x}}\right)$.

See also Problem 143 for an analogous question for sequences of real numbers.

[Er35] Erdős, P., _Note on sequences of integers no one of which is divisible by any
other_. J. London Math. Soc. (1935), 126-128.

[ESS67] Erdős, P., Sárközy, A., and Szemerédi, E., _On a theorem of Behrend_.
J. Austral. Math. Soc. (1967), 9-16.

[ESS68] Erdős, P., Sárközy, A., and Szemerédi, E., _On the solvability of certain
equations in sequences of positive upper logarithmic density_.
J. London Math. Soc. (1968), 71-78.

[Er98] Erdős, P., _Some of my new and almost new problems and results in
combinatorial number theory_. Number theory (Eger, 1996) (1998), 169-180.
-/

namespace Erdos892

/-- A sequence of natural numbers is *primitive* if no element divides any other. -/
def IsPrimitiveSeq (a : ℕ → ℕ) : Prop :=
  ∀ i j, i ≠ j → ¬(a i ∣ a j)

/--
Erdős Problem 892 (particular case) [Er98]:

If $b : \mathbb{N} \to \mathbb{N}$ is a strictly increasing sequence of positive integers such that
$\gcd(b_i, b_j) \neq b_k$ for all pairwise distinct $i, j, k$ (no $b_k$ equals $\gcd(b_i, b_j)$
for pairwise distinct indices),
then there exists a strictly increasing primitive sequence $a : \mathbb{N} \to \mathbb{N}$ with
$a_n \ll b_n$ (i.e. there exists $C$ such that $a_n \leq C \cdot b_n$ for all $n$).
-/
@[category research open, AMS 11]
theorem erdos_892
    (b : ℕ → ℕ)
    (hb_pos : ∀ n, 0 < b n)
    (hb_mono : StrictMono b)
    (hb_gcd : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      Nat.gcd (b i) (b j) ≠ b k) :
    ∃ (a : ℕ → ℕ) (C : ℕ),
      0 < C ∧
      StrictMono a ∧
      IsPrimitiveSeq a ∧
      ∀ n, a n ≤ C * b n := by
  sorry

/--
Erdős Problem 892 (general form) [ESS68] [Er98]:

Characterize which strictly increasing sequences of positive integers $b_1 < b_2 < \cdots$ have the
property that there exists a primitive sequence $a_1 < a_2 < \cdots$ with $a_n \ll b_n$.
-/
@[category research open, AMS 11]
theorem erdos_892.variants.general :
    {b : ℕ → ℕ | (∀ n, 0 < b n) ∧ StrictMono b ∧
      ∃ (a : ℕ → ℕ) (C : ℕ), 0 < C ∧ StrictMono a ∧ IsPrimitiveSeq a ∧
        ∀ n, a n ≤ C * b n} = answer(sorry) := by
  sorry

end Erdos892
