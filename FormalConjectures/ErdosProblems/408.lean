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
# Erdős Problem 408

*References:*
- [erdosproblems.com/408](https://www.erdosproblems.com/408)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
  number theory_. Monographies de L'Enseignement Mathematique (1980).
- [FKL10] Ford, K., Konyagin, S. V. and Luca, F., _Prime chains and Pratt trees_.
  Geom. Funct. Anal. 20 (2010), 1231–1258.
  [arXiv:0904.0473v4](https://arxiv.org/abs/0904.0473v4).
-/

@[expose] public section

namespace Erdos408
open Filter
open scoped Topology

/-- Iteration of Euler's totient, including the zero-fold iterate. -/
abbrev phiIter (k n : ℕ) : ℕ := Nat.totient^[k] n

@[simp, category API, AMS 11]
theorem phi_iter_zero (n : ℕ) : phiIter 0 n = n := rfl

@[simp, category API, AMS 11]
theorem phi_iter_one_input (k : ℕ) : phiIter k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [phiIter, Function.iterate_succ_apply] using ih

/-- Every positive input eventually reaches one. -/
@[category API, AMS 11]
theorem reaches_one (n : ℕ) : 0 < n → ∃ k : ℕ, phiIter k n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      exact ⟨0, rfl⟩
    have hn1 : 1 < n := by omega
    obtain ⟨k, hk⟩ := ih n.totient (Nat.totient_lt n hn1)
      (Nat.totient_pos.mpr hn)
    exact ⟨k + 1, by simpa [phiIter, Function.iterate_succ_apply] using hk⟩

@[category API, AMS 11]
theorem reaches_one_positive (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ phiIter k n = 1 := by
  obtain ⟨k, hk⟩ := reaches_one n.totient (Nat.totient_pos.mpr hn)
  exact ⟨k + 1, Nat.zero_lt_succ k, by simpa [phiIter, Function.iterate_succ_apply] using hk⟩

/-- The minimum positive successful index. The value at zero is a convention. -/
noncomputable def stoppingTime (n : ℕ) : ℕ :=
  if hn : 0 < n then Nat.find (reaches_one_positive n hn) else 0

@[category API, AMS 11]
theorem stopping_time_spec {n : ℕ} (hn : 0 < n) :
    0 < stoppingTime n ∧ phiIter (stoppingTime n) n = 1 := by
  simpa only [stoppingTime, dif_pos hn] using
    (Nat.find_spec (reaches_one_positive n hn))

@[category API, AMS 11]
theorem stopping_time_minimal {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hiter : phiIter k n = 1) : stoppingTime n ≤ k := by
  simpa only [stoppingTime, dif_pos hn] using
    (Nat.find_min' (reaches_one_positive n hn) ⟨hk, hiter⟩)

@[simp, category API, AMS 11]
theorem stopping_time_zero : stoppingTime 0 = 0 := by
  simp [stoppingTime]

@[simp, category API, AMS 11]
theorem stopping_time_one : stoppingTime 1 = 1 := by
  have hpos := (stopping_time_spec (n := 1) (by omega)).1
  have hle := stopping_time_minimal (n := 1) (k := 1)
    (by omega) (by omega) (by simp [phiIter])
  omega

noncomputable def normalizedTime (n : ℕ) : ℝ :=
  (stoppingTime n : ℝ) / Real.log (n : ℝ)

/-- A right-continuous cumulative distribution function. -/
def IsCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧
  (∀ x, Tendsto F (nhdsWithin x (Set.Ici x)) (nhds (F x))) ∧
  Tendsto F atBot (nhds 0) ∧ Tendsto F atTop (nhds 1)

/-- Smoothness at a specified iteration depth depending on the input. -/
def SmoothAtDepth (k : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Set.HasDensity {n | (Nat.maxPrimeFac (phiIter (k n) n) : ℝ) ≤
      Real.rpow (n : ℝ) ε} 1

/-- Explicit rounding convention for the source's illustrative log-log depth. -/
noncomputable def logLogDepth (n : ℕ) : ℕ :=
  ⌊Real.log (Real.log (n : ℝ))⌋₊

def LogLogSmoothness : Prop := SmoothAtDepth logLogDepth

/-- Count of integers up to a real cutoff with a smooth totient iterate. -/
noncomputable def smoothCount (k : ℕ) (x ε : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
    (Nat.maxPrimeFac (phiIter k n) : ℝ) ≤ Real.rpow x ε)).card

/--
Let $\phi(n)$ be the Euler totient function and $\phi_k(n)$ be the iterated $\phi$
function, so that $\phi_1(n)=\phi(n)$ and $\phi_k(n)=\phi(\phi_{k-1}(n))$.
Let $f(n)=\min\{k:\phi_k(n)=1\}$. Does $f(n)/\log n$ have a distribution function?

The minimum is over positive indices. A limiting distribution is specified by a
right-continuous cumulative distribution function, with convergence at its continuity points.
-/
@[category research open, AMS 11]
theorem erdos_408.parts.i : answer(sorry) ↔
    ∃ F : ℝ → ℝ, IsCDF F ∧
      ∀ x : ℝ, ContinuousAt F x →
        Set.HasDensity {n | normalizedTime n ≤ x} (F x) := by
  sorry

/--
Is $f(n)/\log n$ almost always constant?
For every $\epsilon>0$, the exceptional set
$\{n:|f(n)/\log n-c|>\epsilon\}$ is required to have natural density zero.
-/
@[category research open, AMS 11]
theorem erdos_408.parts.ii : answer(sorry) ↔
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      Set.HasDensity {n | ε < |normalizedTime n - c|} 0 := by
  sorry

/--
Ford, Konyagin and Luca [FKL10, Theorem 5] proved that for every $\epsilon,\delta>0$
there is an integer $k$ such that, for all large $x$, at least $(1-\delta)x$ integers
$n\leq x$ satisfy $P^+(\phi_k(n))\leq x^\epsilon$.
-/
@[category research solved, AMS 11]
theorem erdos_408.variants.fixed_depth_smoothness : ∀ ε : ℝ, 0 < ε →
    ∀ δ : ℝ, 0 < δ →
      ∃ k : ℕ, ∀ᶠ x : ℝ in atTop,
        (1 - δ) * x ≤ (smoothCount k x ε : ℝ) := by
  sorry

/--
If $k\to\infty$ however slowly with $n$, then for almost all $n$ the largest prime
factor of $\phi_k(n)$ is $\leq n^{o(1)}$.
This follows from [FKL10, Theorem 5] and monotonicity of the largest prime factor
under totient iteration.
-/
@[category research solved, AMS 11]
theorem erdos_408.variants.arbitrarily_slow_smoothness :
    ∀ k : ℕ → ℕ, Tendsto k atTop atTop →
      ∀ ε : ℝ, 0 < ε →
        Set.HasDensity {n | (Nat.maxPrimeFac (phiIter (k n) n) : ℝ) ≤
          Real.rpow (n : ℝ) ε} 1 := by
  sorry

/--
For $k=\lfloor\log\log n\rfloor$, the largest prime factor of $\phi_k(n)$ is
$\leq n^{o(1)}$ for almost all $n$, as a consequence of [FKL10, Theorem 5].
-/
@[category research solved, AMS 11]
theorem erdos_408.variants.log_log_smoothness : LogLogSmoothness := by
  sorry

end Erdos408
