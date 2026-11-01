/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 952

*References:*
- [erdosproblems.com/952](https://www.erdosproblems.com/952)
- [Wikipedia](https://wikipedia.org/wiki/Gaussian_moat)
- [OAI26a] OpenAI, *Bounded-Step Walks on Gaussian Primes*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf
-/

@[expose] public section


namespace Erdos952

set_option linter.style.formal_proof_palomar false in
/--
Is there an infinite sequence of distinct Gaussian primes $x_1,x_2,\ldots$
such that $\lvert x_{n+1}-x_n\rvert \ll 1$?

No. This was disproved by an internal OpenAI model in September 2026 [OAI26a]; see the linked
Lean proof. It proves `erdos_952.variants.dist`, which implies this statement by
`erdos_952_of_dist`.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/GaussianMoat/Main.lean#L102"]
theorem erdos_952 :
  ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ),
    Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The form of `erdos_952` proved in [OAI26a]: for every $D$, there is no injective sequence of
Gaussian primes $z_0,z_1,\ldots$ with $\lvert z_{t+1}-z_t\rvert \le D$ in $\mathbb{C}$.
This is the first conjunct of the linked theorem.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/GaussianMoat/Main.lean#L102"]
theorem erdos_952.variants.dist :
    ∀ (D : ℝ) (z : ℕ → GaussianInt),
      (∀ t, Irreducible (z t)) → Function.Injective z →
      (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False := by
  sorry

/--
`erdos_952.variants.dist` implies `erdos_952`. A Gaussian prime is irreducible, and the norm of
a Gaussian integer $w$ is $\lvert w\rvert^2$, so $N(x_{n+1}-x_n) < C$ gives
$\lvert x_{n+1}-x_n\rvert \le \sqrt{C}$.
-/
@[category test, AMS 11]
theorem erdos_952_of_dist (h : type_of% erdos_952.variants.dist) : type_of% erdos_952 := by
  rintro ⟨x, C, hx, hC⟩
  refine h √C x (fun n => (hC n).1.irreducible) hx fun n => ?_
  rw [dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm,
    ← GaussianInt.intCast_real_norm]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (hC n).2.le)

end Erdos952
