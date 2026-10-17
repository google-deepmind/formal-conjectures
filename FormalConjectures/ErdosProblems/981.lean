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
# Erdős Problem 981

*References:*
- [erdosproblems.com/981](https://www.erdosproblems.com/981)

*References:*
- [erdosproblems.com/981](https://www.erdosproblems.com/981)
- [El69] Elliott, P. D. T. A., *A conjecture of Erdős concerning character sums*.
  Indag. Math. 31 (1969), 164–171.
- [TaZh25] [arxiv/2512.24631](https://arxiv.org/abs/2512.24631)
  **Average first-passage times for character sums** by *Quanyu Tang and Hao Zhang*

-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos981

def Erdos981Property (ε : ℝ) {p : ℕ} (hp : p.Prime) (N : ℕ) :=
   (∑ n ≤ N, @legendreSym p ⟨hp⟩ n) < ε * N

noncomputable def f (ε : ℝ) {p : ℕ} (hp : p.Prime) : ℕ :=
  sInf { m | ∀ N > m, Erdos981Property ε hp N }

noncomputable def f' (ε : ℝ) {p : ℕ} (hp : p.Prime) : ℕ :=
  sInf { m | Erdos981Property ε hp m }

def S (n : ℕ) := { k | k.Prime ∧ k < n }

/--
TODO: Add description
-/
@[category research solved, AMS 11]
theorem erdos_981 (ε : ℝ) (hε : 0 < ε) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑' p : S ⌊x⌋₊, f ε p.prop.1) * log x / x) atTop (𝓝 c) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_981_alt (ε : ℝ) (hε : 0 < ε) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑' p : S ⌊x⌋₊, f' ε p.prop.1) * log x / x) atTop (𝓝 c) := by
  sorry

end Erdos981
