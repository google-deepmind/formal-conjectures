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
import FormalConjectures.Util.ProblemImports
import FormalConjectures.Arxiv.«2501.03234».Conjecture_1_1
import FormalConjectures.Arxiv.«2501.03234».Conjecture_4_1
/-!
# Conjecture 4.1

*Reference:* [arxiv/2501.03234](https://arxiv.org/abs/2501.03234)
**Theorems and Conjectures on an Arithmetic Sum Associated with the Classical Theta Function θ3**
by *Bruce C. Berndt, Raghavendra N. Bhat, Jeffrey L. Meyer, Likun Xie, Alexandru Zaharescu*
-/
namespace Arxiv.«2501.03234»

def conjecture_4_4_def := ∃(n:ℕ) (Lk : (_:ℕ) → ℕ), ∀ k > Lk n,
    (hprim: Nat.Prime k) → (Odd k) → (n*k < S k)

/--
**Conjecture 4.4**: There exists a natural number n, and a lower bound Lk depending on n, such that
any odd prime k > Lk n, k < S k.
-/
@[category research open, AMS 11]
theorem conjecture_4_4 : conjecture_4_4_def := by
  sorry

example (hc1_1: conjecture_1_1_def) : conjecture_4_4_def :=
  ⟨0,id,fun k hkpos hprim hodd ↦ by simp [hc1_1 k hprim hodd]⟩



end Arxiv.«2501.03234»
