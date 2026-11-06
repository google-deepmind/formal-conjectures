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
# Nonseparability of the three-prime running-LCM kernel

*Reference:* [Cook, No finite separable representation at three prime generators,
Theorem `res:infinite-rank`](https://github.com/wcook04/plectis-erdos/blob/40008384cb6e343c5a93841701ecc25b97974141/paper/269/erdos-269-three-prime-running-lcm.tex#L317-L330).
-/

@[expose] public section

namespace ThreePrimeRunningLcm

open scoped BigOperators

/-- The smooth lattice value attached to the exponent triple $(i,j,k)$. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure prime powers not exceeding $x$.
For pairwise distinct primes and $x \ge 1$, this is the LCM of the positive
$\{p,q,r\}$-smooth integers at most $x$. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The rational reciprocal running-LCM kernel on the smooth lattice. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

@[category test, AMS 11]
theorem smooth3Val_def (p q r i j k : ℕ) :
    smooth3Val p q r i j k = p ^ i * q ^ j * r ^ k := by
  rfl

@[category test, AMS 11]
theorem threePrimeHeight_def (p q r x : ℕ) :
    threePrimeHeight p q r x =
      p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x := by
  rfl

@[category test, AMS 11]
theorem threePrimeKernelQ_def (p q r i j k : ℕ) :
    threePrimeKernelQ p q r i j k =
      (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹ := by
  rfl

/-- For three pairwise distinct primes, the reciprocal running-LCM kernel has
nonsingular minors of every order, with the same row and column indices in
every third-coordinate layer. Consequently it has no finite representation
$K(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)$ over $\mathbb Q$.
This structural statement does not decide the rationality of the scalar
running-LCM series in Erdős Problem 269.

*Source:* Cook, Theorem `res:infinite-rank` in the paper cited above.
-/
@[category research solved, AMS 11 15, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos-lean/blob/2cd19fba5298bc4d8ca9fd469962b18ecfbbca31/verification/FC269UniformKernelCurrent/FC269UniformKernelSolution.lean#L30-L40"]
theorem uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by
  sorry

end ThreePrimeRunningLcm
