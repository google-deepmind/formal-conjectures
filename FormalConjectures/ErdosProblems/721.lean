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
# Erdős Problem 721

*References:*
- [erdosproblems.com/721](https://www.erdosproblems.com/721)
- [Gr22] Green, B., *New lower bounds for van der Waerden numbers*.
  [arXiv:2102.01543](https://arxiv.org/abs/2102.01543).
- [Hu22] Hunter, Z., *Improved lower bounds for van der Waerden numbers*.
  [arXiv:2111.01099](https://arxiv.org/abs/2111.01099).
- [Sc21] Schoen, T., *A subexponential upper bound for van der Waerden numbers W(3,k)*.
  [arXiv:2006.02877](https://arxiv.org/abs/2006.02877).
-/

@[expose] public section

namespace Erdos721

/-- A nonconstant arithmetic progression of length `n` and color `b` in `[1,N]`.
Only positive lengths are used in the research targets. -/
def HasColorAP (f : ℕ → Bool) (b : Bool) (n N : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ a ∧ 0 < d ∧
    ∀ i : ℕ, i < n → a + i * d ≤ N ∧ f (a + i * d) = b

/-- Every coloring has either a red three-term or a blue `k`-term progression.
Here `false` denotes red and `true` denotes blue. -/
def Forces (N k : ℕ) : Prop :=
  ∀ f : ℕ → Bool, HasColorAP f false 3 N ∨ HasColorAP f true k N

/-- Enlarging the interval preserves a progression. -/
@[category API, AMS 5 11]
theorem hasColorAP_mono {f : ℕ → Bool} {b : Bool} {n N M : ℕ}
    (hNM : N ≤ M) (h : HasColorAP f b n N) : HasColorAP f b n M :=
  match h with
  | ⟨a, d, ha, hd, hp⟩ =>
    ⟨a, d, ha, hd, fun i hi =>
      ⟨Nat.le_trans (hp i hi).1 hNM, (hp i hi).2⟩⟩

/-- Enlarging a forcing interval preserves its forcing property. -/
@[category API, AMS 5 11]
theorem forces_mono {N M k : ℕ} (hNM : N ≤ M) (h : Forces N k) : Forces M k :=
  fun f => (h f).elim
    (fun hr => Or.inl (hasColorAP_mono hNM hr))
    (fun hb => Or.inr (hasColorAP_mono hNM hb))

/-- An eventual upper bound by `exp(k^c)`, for one fixed exponent `0 < c < 1`.
Existence of a forcing interval is included explicitly. -/
def SubexponentialUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ K : ℕ, 3 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∃ N : ℕ, Forces N k ∧ (N : ℝ) < Real.exp ((k : ℝ) ^ c)

/-- Hunter's eventual lower bound, in a nonforcing-interval formulation.
The successor `N + 1` is intentional: failure at `N` means the least forcing
integer, when it exists, is at least `N + 1`. The cutoff excludes the
small-input singularities of `log(log k)`. -/
def HunterLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, 3 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∃ N : ℕ, ¬ Forces N k ∧
        Real.exp (c * (Real.log (k : ℝ)) ^ (2 : ℕ) /
          Real.log (Real.log (k : ℝ))) ≤ ((N + 1 : ℕ) : ℝ)

/-- The conjunction of Hunter's lower bound and the subexponential upper bound. -/
def BoundsTarget : Prop := HunterLowerBound ∧ SubexponentialUpperBound

/-- Erdős Problem 721, upper bound: prove that $W(3,k) < \exp(k^c)$ for some
constant $c<1$.

The first to show that $W(3,k) < \exp(k^c)$ for some $c<1$ was Schoen [Sc21].
Source: [erdosproblems.com/721](https://www.erdosproblems.com/721).
The exponent is fixed independently of $k$, and the bound holds for all
sufficiently large $k$. -/
@[category research solved, AMS 5 11]
theorem erdos_721.upper_bound : SubexponentialUpperBound := by
  sorry

/-- Erdős Problem 721, lower bound: Hunter [Hu22] improved this to
$W(3,k) \geq \exp\left(c\frac{(\log k)^2}{\log\log k}\right)$
for some constant $c>0$.

Source: [erdosproblems.com/721](https://www.erdosproblems.com/721).
This eventual bound uses a nonforcing interval of length $N$ and the
successor $N+1$ as a lower bound for the least forcing integer. -/
@[category research solved, AMS 5 11]
theorem erdos_721.lower_bound : HunterLowerBound := by
  sorry

end Erdos721
