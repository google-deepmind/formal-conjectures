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

import Mathlib.Data.Nat.Factorization.Basic

namespace Nat

theorem prod_primeFactors_factorization_apply (n : ℕ) {p : ℕ} (hp : p.Prime) {f : ℕ → ℕ → ℕ}
    (hf : ∀ q n, ¬ q ∣ n → f q n = 0) (hf₀ : ∀ q, f q 0 = 0):
    (∏ q ∈ n.primeFactors, q ^ f q n).factorization p = f p n := by
  rw [factorization_prod fun _ _ _ ↦ by simp_all, Finset.sum_congr rfl fun x hx ↦ by
      rw [factorization_pow, (mem_primeFactors.1 hx).1.factorization]]
  by_cases hpn : p ∣ n <;> simp [Finsupp.single_apply, hp, hpn]
  · exact fun _ ↦ by simp_all [hf₀]
  · simp [hf _ _ hpn]

end Nat
