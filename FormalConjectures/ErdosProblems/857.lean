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
# Erdős Problem 857

*References:*
- [erdosproblems.com/857](https://www.erdosproblems.com/857)
- [Er70] Erdős, P., *Some extremal problems in combinatorial number theory*. Mathematical Essays
  Dedicated to A. J. Macintyre (1970), 123-133. [PDF](https://www.renyi.hu/~p_erdos/1970-21.pdf)
- [BHL26] Bucić, M., He, F. and Lee, H., *Proof of the Erdős-Szemerédi sunflower conjecture*.
  [arXiv:2610.26686](https://arxiv.org/abs/2610.26686) (2026).
-/

@[expose] public section

open Filter

namespace Erdos857

/--
`m(n, k)`: minimal sunflower-forcing family size in the non-uniform `[n]` model.
-/
noncomputable def m (n k : ℕ) : ℕ :=
  sInf {t : ℕ | ∀ (F : Set (Set (Fin n))), t ≤ F.ncard →
    ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/--
Let $m=m(n,k)$ be minimal such that in any collection of sets
$A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ there must exist a sunflower of size $k$ - that is, some
collection of $k$ of the $A_i$ which pairwise have the same intersection.

Estimate $m(n,k)$. In particular, is it true that, for some $c_k>0$,
$$m(n,k) \leq (2-c_k)^n?$$

The bound is stated for all large $n$: $m(1,3) = 3 > 2 - c$ for every $c > 0$.
Bucić, He and Lee [BHL26] proved it for every $k \geq 3$.
-/
@[category research solved, question, AMS 5]
theorem erdos_857 :
    ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, (m n k : ℝ) ≤ (2 - c) ^ n := by
  sorry

def erdos_857.variants.asymptotic.answer : ℕ → ℕ → ℝ := sorry

/--
Estimate $m(n,k)$, or better give an asymptotic formula.
-/
@[category research open, question value, AMS 5]
theorem erdos_857.variants.asymptotic :
    ∀ k : ℕ, 3 ≤ k →
      Tendsto (fun n : ℕ => (m n k : ℝ) / erdos_857.variants.asymptotic.answer k n) atTop
        (nhds 1) := by
  sorry

end Erdos857
