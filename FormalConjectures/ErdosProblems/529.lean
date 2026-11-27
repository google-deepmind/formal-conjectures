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
# Erdős Problem 529

*References:*
- [erdosproblems.com/529](https://www.erdosproblems.com/529)
- [DuHa13] Duminil-Copin, Hugo and Hammond, Alan, *Self-avoiding walk is sub-ballistic*. Comm.
  Math. Phys. (2013), 401-423.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [HaSl91] Hara, Takashi and Slade, Gordon, *Critical behaviour of self-avoiding walk in five or
  more dimensions*. Bull. Amer. Math. Soc. (N.S.) (1991), 417-423.
- [HaSl92] Hara, Takashi and Slade, Gordon, *Self-avoiding walk in five or more dimensions. I. The
  critical behaviour*. Comm. Math. Phys. (1992), 101-136.
- [MaSl93] Madras, Neal and Slade, Gordon, *The self-avoiding walk*. (1993), xiv+425.
- [Sl87] Slade, Gordon, *The diffusion of self-avoiding random walk in high dimensions*. Comm.
  Math. Phys. (1987), 661-683.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos529

/-- The unit step in $\mathbb{Z}^k$ in direction `i`, positive if `b` is true and negative
otherwise. -/
def step {k : ℕ} (s : Fin k × Bool) : Fin k → ℤ :=
  Pi.single s.1 (if s.2 then 1 else -1)

/-- The position after the first `j` steps of the walk with steps `w`, starting at the origin. -/
def position {k n : ℕ} (w : Fin n → Fin k × Bool) (j : ℕ) : Fin k → ℤ :=
  ∑ t : Fin n with t.val < j, step (w t)

/-- The walk with steps `w` is self-avoiding: its positions after $0, 1, \ldots, n$ steps are
distinct. -/
def IsSelfAvoiding {k n : ℕ} (w : Fin n → Fin k × Bool) : Prop :=
  Function.Injective fun j : Fin (n + 1) ↦ position w j

/-- The self-avoiding walks of `n` steps in $\mathbb{Z}^k$ starting at the origin. -/
noncomputable def selfAvoidingWalks (k n : ℕ) : Finset (Fin n → Fin k × Bool) := by
  classical
  exact Finset.univ.filter IsSelfAvoiding

/-- The Euclidean distance from the origin of a point of $\mathbb{Z}^k$. -/
noncomputable def dist0 {k : ℕ} (p : Fin k → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((p i : ℝ)) ^ 2)

/-- $d_k(n)$: the expected distance from the origin of the endpoint of a uniformly random
self-avoiding walk of `n` steps in $\mathbb{Z}^k$. -/
noncomputable def d (k n : ℕ) : ℝ :=
  (∑ w ∈ selfAvoidingWalks k n, dist0 (position w n)) / (selfAvoidingWalks k n).card

/--
Let $d_k(n)$ be the expected distance from the origin after taking $n$ random steps from the
origin in $\mathbb{Z}^k$ (conditional on no self intersections), that is, a self-avoiding walk.
Is it true that
$$\lim_{n\to\infty}\frac{d_2(n)}{n^{1/2}}=\infty?$$
-/
@[category research open, question, AMS 60 82]
theorem erdos_529 :
    Tendsto (fun n : ℕ ↦ d 2 n / Real.sqrt n) atTop atTop := by
  sorry

/--
Is it true that $d_k(n)\ll n^{1/2}$ for $k\geq 3$?

It is now conjectured that this is false for $k=3$ and $k=4$ (see [MaSl93, Section 1.4]).
-/
@[category research open, question, AMS 60 82]
theorem erdos_529.variants.ge_three :
    ∀ k ≥ 3, (fun n : ℕ ↦ d k n) =O[atTop] (fun n : ℕ ↦ Real.sqrt n) := by
  sorry

/--
Hara and Slade [HaSl91, HaSl92] proved that, for all $k\geq 5$, $d_k(n)\sim Dn^{1/2}$ for some
constant $D>0$. Slade [Sl87] had proved this for all sufficiently large $k$.
-/
@[category research solved, AMS 60 82]
theorem erdos_529.variants.hara_slade (k : ℕ) (hk : 5 ≤ k) :
    ∃ D > 0, Tendsto (fun n : ℕ ↦ d k n / Real.sqrt n) atTop (nhds D) := by
  sorry

/--
Duminil-Copin and Hammond [DuHa13] proved that $d_2(n)=o(n)$.
-/
@[category research solved, AMS 60 82]
theorem erdos_529.variants.duminil_copin_hammond :
    (fun n : ℕ ↦ d 2 n) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  sorry

end Erdos529
