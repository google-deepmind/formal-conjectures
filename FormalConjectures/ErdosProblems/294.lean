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
# Erdős Problem 294

*References:*
- [erdosproblems.com/294](https://www.erdosproblems.com/294)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  [arXiv:2404.07113](https://arxiv.org/abs/2404.07113) (2024).
-/

@[expose] public section

open Filter

namespace Erdos294

/-- `HasUnitFractionSolution m N` says that $1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ for some
integers $m=n_1<\cdots<n_k\leq N$: the $n_i$ form a finite set `s` whose least element is `m`. -/
def HasUnitFractionSolution (m N : ℕ) : Prop :=
  ∃ s : Finset ℕ, m ∈ s ∧ (∀ n ∈ s, m ≤ n ∧ n ≤ N) ∧ ∑ n ∈ s, (1 : ℚ) / n = 1

/-- $t(N)$: the least positive integer $t$ such that there is no solution to
$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ with $t=n_1<\cdots<n_k\leq N$. The set of candidates
contains $N+1$, so `sInf` is a true minimum. -/
noncomputable def t (N : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ¬ HasUnitFractionSolution m N}

/-- For $N\geq 1$ the solution $1=\frac11$ shows that $t=1$ is not a candidate. -/
@[category API, AMS 11]
theorem hasUnitFractionSolution_one {N : ℕ} (hN : 1 ≤ N) : HasUnitFractionSolution 1 N :=
  ⟨{1}, by simp, by simpa using hN, by simp⟩

/-- The set defining $t(N)$ contains $N+1$, so $t(N)\leq N+1$. -/
@[category API, AMS 11]
theorem t_le_succ (N : ℕ) : t N ≤ N + 1 :=
  Nat.sInf_le ⟨Nat.succ_pos N, fun h => by
    obtain ⟨s, hs, hall, -⟩ := h
    have := (hall _ hs).2
    omega⟩

/--
Let $N\geq 1$ and let $t(N)$ be the least integer $t$ such that there is no solution to
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
with $t=n_1<\cdots <n_k\leq N$. Estimate $t(N)$.

Solved by Liu and Sawhney [LiSa24, Theorem 1.6] (up to $(\log\log N)^{O(1)}$), who proved that
$$\frac{N}{(\log N)(\log\log N)^3(\log\log\log N)^{O(1)}}\ll t(N) \ll \frac{N}{\log N}.$$
The unspecified $O(1)$ exponent is the real number `K`.
-/
@[category research solved, AMS 11]
theorem erdos_294 :
    (∃ K : ℝ, (fun N : ℕ => (N : ℝ) / (Real.log N * Real.log (Real.log N) ^ 3 *
        Real.log (Real.log (Real.log N)) ^ K)) ≪ (fun N : ℕ => (t N : ℝ))) ∧
    ((fun N : ℕ => (t N : ℝ)) ≪ (fun N : ℕ => (N : ℝ) / Real.log N)) := by
  sorry

/--
Erdős and Graham [ErGr80, p. 35] could show that $t(N)\ll\frac{N}{\log N}$. They gave no proof;
one is in [LiSa24, Section 4].
-/
@[category research solved, AMS 11]
theorem erdos_294.variants.erdos_graham_upper :
    (fun N : ℕ => (t N : ℝ)) ≪ (fun N : ℕ => (N : ℝ) / Real.log N) := by
  sorry

end Erdos294
