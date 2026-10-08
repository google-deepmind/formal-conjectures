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
# Erdős Problem 378

*References:*
- [erdosproblems.com/378](https://www.erdosproblems.com/378)
- [ErGr80] Erdős, P. and Graham, R. L., Old and new problems and results in
  combinatorial number theory (1980), p. 72.
- [GrRa96] Granville, Andrew and Ramaré, Olivier, Explicit bounds on exponential sums
  and the scarcity of squarefree binomial coefficients. Mathematika (1996), 73–107.
-/

@[expose] public section

namespace Erdos378

open Filter Topology

/-- The number of $k$ with $1\leq k<n$ for which $\binom{n}{k}$ is squarefree. -/
def sqfreeBinomCount (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun k => Squarefree (n.choose k))).card

/-- The number of $n<N$ with at least $r$ squarefree nontrivial binomial coefficients. -/
def countUpTo (r N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => r ≤ sqfreeBinomCount n)).card

/--
Let $r\geq 0$. Does the density of integers $n$ for which $\binom{n}{k}$ is squarefree
for at least $r$ values of $1\leq k<n$ exist? Is this density $>0$?

Aggarwal and Cambie have observed this problem is resolved by the results of Granville
and Ramaré [GrRa96].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos378.lean#L3256"]
theorem erdos_378 : answer(True) ↔
    ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧
      Tendsto (fun N : ℕ => (countUpTo r N : ℝ) / N) atTop (𝓝 d) := by
  sorry

/--
For every $r$, the set of $n$ with at least $r$ squarefree binomial coefficients
$\binom{n}{k}$, $1\leq k<n$, has positive lower density. This follows from [GrRa96].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos378.lean#L3256"]
theorem erdos_378.variants.lower_density_pos (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * N ≤ (countUpTo r N : ℝ) := by
  sorry

/-- Any existing density is positive, by the positive lower density bound. -/
@[category API, AMS 11]
theorem density_pos_of_tendsto (r : ℕ) (d : ℝ)
    (hd : Tendsto (fun N : ℕ => (countUpTo r N : ℝ) / N) atTop (𝓝 d)) : 0 < d := by
  obtain ⟨c, hc, hev⟩ := erdos_378.variants.lower_density_pos r
  refine lt_of_lt_of_le hc (ge_of_tendsto hd ?_)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  rw [le_div_iff₀ (by exact_mod_cast hN0)]
  exact hN

/-- For $r=0$, every integer is counted, so the density is $1$. -/
@[category textbook, AMS 11]
theorem erdos_378.variants.zero :
    Tendsto (fun N : ℕ => (countUpTo 0 N : ℝ) / N) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp [countUpTo, hN.ne']

@[category test, AMS 11]
example : sqfreeBinomCount 0 = 0 := by decide +kernel

@[category test, AMS 11]
example : sqfreeBinomCount 1 = 0 := by decide +kernel

@[category test, AMS 11]
example : sqfreeBinomCount 6 = 4 := by decide +kernel

@[category test, AMS 11]
example : sqfreeBinomCount 4 = 1 := by decide +kernel

end Erdos378
