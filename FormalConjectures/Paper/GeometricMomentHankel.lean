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
# Fixed-base asymptotic of geometric-moment Hankel determinants

The normalized moments below are those in Zudilin's generalized $q$-logarithm
construction at $x=z=1$. The paper determines their Hankel determinant's
asymptotic size for each fixed real $0<q<1$.

*References:*
- [Cook, Erdős #1049 rational-base Lambert paper, Theorem `res:sharp-fixed-base`](https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/1049/erdos-1049-rational-base-lambert.tex#L740-L747).
- [Zudilin, On the irrationality of generalized $q$-logarithm](https://arxiv.org/abs/1601.02688v2),
  Res. Number Theory 2 (2016), Art. 15; equation (6), Section 4 and Lemma 1.
-/

@[expose] public section

namespace GeometricMomentHankel

open Filter Finset
open scoped Topology BigOperators

/-- The factorial coefficient $C_N=(N!)^2(N+1)!/2^N$. -/
noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- The finite $q$-product $(a;q)_n$. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
/-- The infinite $q$-product, expressed through its logarithmic series. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
/-- The summand of Zudilin's normalized moment at $x=z=1$. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)
/-- Zudilin's normalized moment $v_m^*(q)$. -/
noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t
/-- The Hankel matrix $(v_{i+j}^*(q))_{0\le i,j<N}$. -/
noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)
/-- The term $z^n/(1-z^n)$ of the Lambert series. -/
noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)
/-- The Lambert series $\sum_{n\ge0}z^n/(1-z^n)$; the zeroth term is zero. -/
noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n

/-- The empty finite product is one. -/
@[category API, AMS 33]
theorem qPochhammerFinite_zero (a q : ℝ) : qPochhammerFinite a q 0 = 1 := by
  simp [qPochhammerFinite]

/-- The Hankel entry uses the sum of the two indices. -/
@[category API, AMS 15]
theorem actualMomentHankel_apply (q : ℝ) (N : ℕ) (i j : Fin N) :
    actualMomentHankel q N i j = actualMoment q (i.val + j.val) := by
  rfl

/--
For each fixed $0<q<1$, there is $K(q)>0$ such that
$V_N^*(q)\sim K(q)C_Nq^{N(N-1)(2N-1)/6}P^{2N}N^{-8F(1/q)}$,
where $V_N^*(q)$ is the determinant of the normalized moment matrix,
$C_N=(N!)^2(N+1)!/2^N$, $P=(q;q)_\infty$, and
$F(1/q)=\sum_{n\ge1}q^n/(1-q^n)$.

Cook's fixed-base theorem refines Zudilin's formal-order lower bound and
fixed-base size estimate from the 2016 paper. It asserts convergence of the
displayed ratio to one for each fixed base, with no uniformity as $q\to1$.
It does not settle irrationality of the Lambert value at every rational base.
-/
@[category research solved, AMS 11 15 40, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_08/PaperStatementsU.lean#L25-L30"]
theorem fixed_base_asymptotic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := by
  sorry

end GeometricMomentHankel
