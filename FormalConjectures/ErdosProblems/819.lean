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
# Erdős Problem 819

*References:*
- [erdosproblems.com/819](https://www.erdosproblems.com/819)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196-205.
-/

@[expose] public section

open Filter Asymptotics
open scoped Finset Pointwise

namespace Erdos819

/-- $f(N)$ is the maximum of $\lvert (A + A) \cap [1, N] \rvert$ over all
$A \subseteq \{1, \ldots, N\}$ with $\lvert A \rvert = \lfloor N^{1/2} \rfloor$, where
$\lfloor N^{1/2} \rfloor$ is `Nat.sqrt N`. Such sets exist for every $N$, since
$\lfloor N^{1/2} \rfloor \leq N$, so the maximum is over a nonempty family. -/
def f (N : ℕ) : ℕ :=
  (Finset.powersetCard (Nat.sqrt N) (Finset.Icc 1 N)).sup
    fun A ↦ #((A + A) ∩ Finset.Icc 1 N)

/-- Trivial upper bound: $f(N) \leq N$. -/
@[category API, AMS 5 11]
theorem f_le (N : ℕ) : f N ≤ N := by
  refine Finset.sup_le fun A _ ↦ ?_
  calc #((A + A) ∩ Finset.Icc 1 N) ≤ #(Finset.Icc 1 N) :=
        Finset.card_le_card Finset.inter_subset_right
    _ = N := by simp

/-- Every sum $a + b$ with $a, b \in A$ comes from an unordered pair $\{a, b\}$, so
$\lvert A + A\rvert \leq \binom{\lvert A\rvert + 1}{2}$. -/
@[category API, AMS 5 11]
theorem card_add_self_le (A : Finset ℕ) : #(A + A) ≤ (#A + 1).choose 2 := by
  rw [← Finset.card_sym2]
  calc #(A + A) ≤ #(A.sym2.image (Sym2.lift ⟨fun a b ↦ a + b, fun a b ↦ add_comm a b⟩)) := by
        refine Finset.card_le_card fun x hx ↦ ?_
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
        exact Finset.mem_image.2 ⟨s(a, b), Finset.mk_mem_sym2_iff.2 ⟨ha, hb⟩, rfl⟩
    _ ≤ #A.sym2 := Finset.card_image_le

/-- With $k = \lfloor N^{1/2} \rfloor$, we have $f(N) \leq \binom{k+1}{2} = (k^2 + k)/2$, and
$k^2 \leq N$, $k \leq N^{1/2}$. -/
@[category API, AMS 5 11]
theorem f_le_half_add_sqrt (N : ℕ) : (f N : ℝ) ≤ (N + Real.sqrt N) / 2 := by
  have hf : f N ≤ (Nat.sqrt N + 1).choose 2 := by
    refine Finset.sup_le fun A hA ↦ ?_
    rw [← (Finset.mem_powersetCard.1 hA).2]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (card_add_self_le A)
  have hsq : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hle : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  calc (f N : ℝ) ≤ ((Nat.sqrt N + 1).choose 2 : ℕ) := by exact_mod_cast hf
    _ = ((Nat.sqrt N : ℝ) ^ 2 + Nat.sqrt N) / 2 := by
        rw [Nat.cast_choose_two]; push_cast; ring
    _ ≤ (N + Real.sqrt N) / 2 := by linarith

def erdos_819.answer : ℕ → ℝ := sorry

/--
Let $f(N)$ be maximal such that there exists $A\subseteq \{1,\ldots,N\}$ with
$\lvert A\rvert=\lfloor N^{1/2}\rfloor$ such that $\lvert (A+A)\cap [1,N]\rvert=f(N)$.
Estimate $f(N)$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_819 : (fun N ↦ (f N : ℝ)) ~[atTop] erdos_819.answer := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{3}{8}-o(1)\right)N \leq f(N) \leq \left(\frac{1}{2}+o(1)\right)N.$$

This is the lower bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_819.variants.erdos_freud_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (3 / 8 - ε) * N ≤ (f N : ℝ) := by
  sorry

/--
Erdős and Freud [ErFr91] proved
$$\left(\frac{3}{8}-o(1)\right)N \leq f(N) \leq \left(\frac{1}{2}+o(1)\right)N.$$

This is the upper bound.
-/
@[category research solved, AMS 5 11]
theorem erdos_819.variants.erdos_freud_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (1 / 2 + ε) * N := by
  intro ε hε
  filter_upwards [eventually_ge_atTop ⌈1 / (4 * ε ^ 2)⌉₊] with N hN
  have hN' : 1 / (4 * ε ^ 2) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h1 : 1 ≤ 4 * ε ^ 2 * N := by
    rw [div_le_iff₀ (by positivity)] at hN'
    linarith
  -- $\sqrt{N} \leq 2\varepsilon N$, since $N \leq (2\varepsilon N)^2$ once $4\varepsilon^2 N \geq 1$.
  have hs : Real.sqrt N ≤ 2 * ε * N := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith [f_le_half_add_sqrt N]

end Erdos819
