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
# Erdős Problem 177

*References:*
- [erdosproblems.com/177](https://www.erdosproblems.com/177)
- [Er66] Erdős, P., *Remarks on number theory. V. Extremal problems in number theory. II*.
  Mat. Lapok 17 (1966), 135-155.
- [Ro64] Roth, K. F., *Remark concerning integer sequences*. Acta Arith. (1964), 257-260.
- [Be17] Beck, József, *A discrepancy problem: balancing infinite dimensional vectors*.
  Number theory—Diophantine problems, uniform distribution and applications (2017), 61-82.
-/

@[expose] public section

namespace Erdos177

open Finset Filter Asymptotics

/-- `IsAdmissible h` means that there is $f : \mathbb{N} \to \{-1, 1\}$ such that, for every
$d \geq 1$, every finite arithmetic progression $P_d$ of positive integers with common
difference $d$ satisfies $\left\lvert \sum_{n \in P_d} f(n) \right\rvert \leq h(d)$. -/
def IsAdmissible (h : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ d ≥ 1, ∀ a ≥ 1, ∀ N : ℕ, |((∑ i ∈ range N, f (a + i * d) : ℤ) : ℝ)| ≤ h d

/-- `H` is the optimal growth rate for Erdős Problem 177: some admissible `h` is `O(H)`,
and `H` is `O(h)` for every admissible `h`. -/
def IsOptimalGrowth (H : ℕ → ℝ) : Prop :=
  (∃ h, IsAdmissible h ∧ h =O[atTop] H) ∧ ∀ h, IsAdmissible h → H =O[atTop] h

/-- The maximum of $h(d)$ over $1 \leq d \leq D$, with value zero at $D=0$. -/
noncomputable def runningMax (h : ℕ → ℝ) (D : ℕ) : ℝ :=
  if hD : 1 ≤ D then
    (Icc 1 D).sup' ⟨1, mem_Icc.mpr ⟨le_rfl, hD⟩⟩ h
  else 0

/-- The running maximum at zero is zero. -/
@[category API, AMS 5 11]
theorem runningMax_zero (h : ℕ → ℝ) : runningMax h 0 = 0 := by
  simp [runningMax]

/-- Every value at a positive index is bounded by the running maximum. -/
@[category API, AMS 5 11]
theorem le_runningMax (h : ℕ → ℝ) {d D : ℕ} (hd : 1 ≤ d) (hdD : d ≤ D) :
    h d ≤ runningMax h D := by
  rw [runningMax, dif_pos (hd.trans hdD)]
  exact le_sup' h (mem_Icc.mpr ⟨hd, hdD⟩)

/--
Find the smallest $h(d)$ such that the following holds. There exists a function
$f : \mathbb{N} \to \{-1, 1\}$ such that, for every $d \geq 1$,
$$\max_{P_d} \left\lvert \sum_{n \in P_d} f(n) \right\rvert \leq h(d),$$
where $P_d$ ranges over all finite arithmetic progressions with common difference $d$.

We formalise "smallest" as the optimal growth rate of $h$, up to constant factors.
-/
@[category research open, AMS 5 11]
theorem erdos_177 : IsOptimalGrowth (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Cantor, Erdős, Schreiber and Straus [Er66]: $h(d) \ll d!$ is possible. -/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/AItoBit/erdos-177-lean/blob/main/Erdos177.lean#L281"]
theorem erdos_177.variants.factorial :
    ∃ h, IsAdmissible h ∧ h =O[atTop] (fun d : ℕ => (d.factorial : ℝ)) := by
  sorry

/-- Beck [Be17]: $h(d) \ll d^{8 + \varepsilon}$ is possible for every $\varepsilon > 0$. -/
@[category research solved, AMS 5 11]
theorem erdos_177.variants.beck (ε : ℝ) (hε : 0 < ε) :
    ∃ h, IsAdmissible h ∧ h =O[atTop] (fun d : ℕ => (d : ℝ) ^ (8 + ε)) := by
  sorry

/-- Roth [Ro64, p. 258, (4)] implies that every admissible $h$ satisfies
$\max_{1 \leq d \leq D} h(d) \gg D^{1/2}$. The step giving a large discrepancy
may depend on $D$; admissible bounds need not be monotone. -/
@[category research solved, AMS 5 11]
theorem erdos_177.variants.roth (h : ℕ → ℝ) (hh : IsAdmissible h) :
    (fun D : ℕ => Real.sqrt D) =O[atTop] runningMax h := by
  sorry

/-- By van der Waerden's theorem, no admissible $h$ is bounded. -/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/AItoBit/erdos-177-lean/blob/main/Erdos177.lean#L324"]
theorem erdos_177.variants.not_bounded (h : ℕ → ℝ) (hh : IsAdmissible h) :
    ¬ ∃ C : ℝ, ∀ d ≥ 1, h d ≤ C := by
  sorry

end Erdos177
