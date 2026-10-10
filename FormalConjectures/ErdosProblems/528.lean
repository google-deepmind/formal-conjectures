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
# Erdős Problem 528

*References:*
- [erdosproblems.com/528](https://www.erdosproblems.com/528)
- [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int.
  Közl. (1961), 221–254, p. 254.
- [HM54] Hammersley, J. M. and Morton, K. W., _Poor man's Monte Carlo_. J. Roy.
  Statist. Soc. Ser. B (1954), 23–38; discussion 61–75.
- [JSG16] Jacobsen, Jesper Lykke, Scullard, Christian R., and Guttmann, Anthony J.,
  _On the growth constant for square-lattice self-avoiding walks_. J. Phys. A (2016),
  494004. [arXiv:1607.02984](https://arxiv.org/abs/1607.02984)
- [GL17] Grimmett, Geoffrey R. and Li, Zhongyang, _Self-avoiding walks and
  connective constants_. [arXiv:1704.05884](https://arxiv.org/abs/1704.05884)
- [Co22] Couronné, Olivier, _New upper bound for the connective constant for
  square-lattice self-avoiding walks_. [arXiv:2211.16146](https://arxiv.org/abs/2211.16146)
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos528

/-- A signed coordinate direction in $\mathbb Z^k$. -/
abbrev Direction (k : ℕ) := Fin k × Bool

/-- The unit displacement associated with a signed coordinate direction. -/
def displacement {k : ℕ} (d : Direction k) : Fin k → ℤ :=
  fun i => if i = d.1 then if d.2 then 1 else -1 else 0

/-- The $n+1$ visited vertices of a direction word of length $n$, starting at zero. -/
def vertices {k n : ℕ} (w : Fin n → Direction k) (t : Fin (n + 1)) : Fin k → ℤ :=
  ∑ j : Fin n, if j.val < t.val then displacement (w j) else 0

/-- A direction word is self-avoiding when all its visited vertices are distinct. -/
def IsSelfAvoiding {k n : ℕ} (w : Fin n → Direction k) : Prop :=
  Function.Injective (vertices w)

instance {k n : ℕ} (w : Fin n → Direction k) : Decidable (IsSelfAvoiding w) :=
  inferInstanceAs (Decidable (Function.Injective (vertices w)))

/-- The number of self-avoiding walks of $n$ steps from the origin in $\mathbb Z^k$.
Each walk is encoded by its sequence of signed coordinate directions. -/
def walkCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Direction k => IsSelfAvoiding w)).card

@[simp, category API, AMS 5]
theorem vertices_zero {k n : ℕ} (w : Fin n → Direction k) : vertices w 0 = 0 := by
  simp [vertices]

@[category API, AMS 5]
theorem displacement_ne_zero {k : ℕ} (d : Direction k) : displacement d ≠ 0 := by
  intro h
  have h' := congrFun h d.1
  cases hd : d.2 <;> simp [displacement, hd] at h'

@[simp, category API, AMS 5]
theorem walkCount_zero (k : ℕ) : walkCount 0 k = 1 := by
  classical
  have h (w : Fin 0 → Direction k) : IsSelfAvoiding w := by
    intro i j _
    exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  simp [walkCount, h]

@[category API, AMS 5]
theorem walkCount_le (n k : ℕ) : walkCount n k ≤ (2 * k) ^ n := by
  classical
  calc
    walkCount n k ≤ Fintype.card (Fin n → Direction k) := Finset.card_filter_le _ _
    _ = (2 * k) ^ n := by simp [Direction, Nat.mul_comm]

/-- Let $f(n,k)$ count the number of self-avoiding walks of $n$ steps (beginning at
the origin) in $\mathbb{Z}^k$ (i.e. those walks which do not intersect themselves).
Determine $C_k=\lim_{n\to\infty}f(n,k)^{1/n}$.

The dimension is positive; $\mathbb Z^0$ has no nontrivial walks. -/
@[category research open, AMS 5 60]
theorem erdos_528 :
    (answer(sorry) : ℕ → ℝ) ∈ {C | ∀ k : ℕ, 0 < k →
      Tendsto (fun n : ℕ => (walkCount n k : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (C k))} := by
  sorry

/-- Hammersley and Morton [HM54] showed that the connective constant exists. -/
@[category research solved, AMS 5 60]
theorem erdos_528.variants.limit_exists (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, Tendsto (fun n : ℕ => (walkCount n k : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 C) := by
  sorry

end Erdos528
