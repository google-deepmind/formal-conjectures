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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 3

*References:*
- [erdosproblems.com/3](https://www.erdosproblems.com/3)
- [BlSi20] Bloom, Thomas F. and Sisask, Olof, *Breaking the logarithmic barrier in Roth's theorem
  on arithmetic progressions*. arXiv:2007.03528 (2020).
- [Go01] Gowers, W. T., *A new proof of Szemerédi's theorem*. Geom. Funct. Anal. (2001), 465-588.
- [GrTa17] Green, Ben and Tao, Terence, *New bounds for Szemerédi's theorem, III: a
  polylogarithmic bound for $r_4(N)$*. Mathematika (2017).
- [KeMe23] Kelley, Zander and Meka, Raghu, *Strong bounds for 3-progressions*. 2023 IEEE 64th
  Annual Symposium on Foundations of Computer Science (FOCS) (2023).
- [LSS24] Leng, James, Sah, Ashwin and Sawhney, Mehtaab, *Improved bounds for Szemerédi's
  theorem*. arXiv:2402.17995 (2024).
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos3

/--
If $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?
-/
@[category research open, AMS 11]
theorem erdos_3 : answer(sorry) ↔ ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  sorry

/--
The case of $3$-term progressions: if $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$,
then $A$ contains a non-trivial $3$-term arithmetic progression.

Proved by Bloom and Sisask [BlSi20].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.three : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength 3 := by
  sorry

/--
$r_k(N)$ is the largest size of a subset of $\{1, \dots, N\}$ that does not contain a non-trivial
$k$-term arithmetic progression.
-/
noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/--
There are $\beta > 0$ and $c > 0$ such that $r_3(N) \ll N \exp(-c (\log N)^{\beta})$.

Proved by Kelley and Meka [KeMe23].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.kelley_meka : ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (r 3 N : ℝ)) =O[atTop] fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β) := by
  sorry

/--
There is $c > 0$ such that $r_4(N) \ll N (\log N)^{-c}$.

Proved by Green and Tao [GrTa17].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.green_tao : ∃ c > (0 : ℝ),
    (fun N ↦ (r 4 N : ℝ)) =O[atTop] fun N : ℕ ↦ (N : ℝ) * Real.log N ^ (-c) := by
  sorry

/--
For every $k \geq 3$ there is $c_k > 0$ such that $r_k(N) \ll_k N (\log \log N)^{-c_k}$.

Proved by Gowers [Go01].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.gowers (k : ℕ) (hk : 3 ≤ k) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) =O[atTop] fun N : ℕ ↦ (N : ℝ) * Real.log (Real.log N) ^ (-c) := by
  sorry

/--
For every $k \geq 5$ there is $c_k > 0$ such that $r_k(N) \ll_k N \exp(-(\log \log N)^{c_k})$.

Proved by Leng, Sah and Sawhney [LSS24].
-/
@[category research solved, AMS 11]
theorem erdos_3.variants.leng_sah_sawhney (k : ℕ) (hk : 5 ≤ k) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) =O[atTop]
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c) := by
  sorry

end Erdos3
