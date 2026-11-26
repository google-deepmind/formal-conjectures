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
# Erdős Problem 389

*Reference:* [erdosproblems.com/389](https://www.erdosproblems.com/389)
-/

@[expose] public section

namespace Erdos389

/--
Is it true that for every $n \geq 1$ there is a $k$ such that
$$
  n(n + 1) \cdots (n + k - 1) \mid (n + k) \cdots (n + 2k - 1)?
$$
-/
@[category research open, question, AMS 11]
theorem erdos_389 :
    ∀ n ≥ 1, ∃ k ≥ 1, ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i) := by
  sorry

/--
Bhavik Mehta has computed the minimal such $k$ for $1 \leq n \leq 18$.
For example, the minimal $k$ for $n = 4$ is $207$.
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_four :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (4 + i) ∣ ∏ i ∈ Finset.range k, (4 + k + i) }
      207 := by
  refine ⟨⟨by norm_num, by native_decide⟩, ?_⟩
  intro k ⟨_, hdvd⟩
  by_contra! hlt
  interval_cases k <;> revert hdvd <;> native_decide

/--
The minimal $k$ for $n = 1$ is $1$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_one :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (1 + i) ∣ ∏ i ∈ Finset.range k, (1 + k + i) }
      1 := by
  have hlt : ∀ k < 1, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (1 + i) ∣ ∏ i ∈ Finset.range k, (1 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

/--
The minimal $k$ for $n = 2$ is $5$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_two :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i) }
      5 := by
  have hlt : ∀ k < 5, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

/--
The minimal $k$ for $n = 3$ is $4$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_three :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i) }
      4 := by
  have hlt : ∀ k < 4, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

/--
The minimal $k$ for $n = 5$ is $206$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_five :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (5 + i) ∣ ∏ i ∈ Finset.range k, (5 + k + i) }
      206 := by
  have hlt : ∀ k < 206, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (5 + i) ∣ ∏ i ∈ Finset.range k, (5 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

/--
The minimal $k$ for $n = 6$ is $2475$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_six :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (6 + i) ∣ ∏ i ∈ Finset.range k, (6 + k + i) }
      2475 := by
  have hlt : ∀ k < 2475, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (6 + i) ∣ ∏ i ∈ Finset.range k, (6 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

/--
The minimal $k$ for $n = 7$ is $984$ (Bhavik Mehta's table, OEIS A375071).
-/
@[category textbook, AMS 11]
theorem erdos_389.variants.mehta_seven :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (7 + i) ∣ ∏ i ∈ Finset.range k, (7 + k + i) }
      984 := by
  have hlt : ∀ k < 984, 1 ≤ k →
      ¬ ∏ i ∈ Finset.range k, (7 + i) ∣ ∏ i ∈ Finset.range k, (7 + k + i) := by
    native_decide
  refine ⟨⟨by norm_num, by native_decide⟩, fun k ⟨hk1, hk⟩ => ?_⟩
  by_contra! h
  exact hlt k h hk1 hk

end Erdos389
