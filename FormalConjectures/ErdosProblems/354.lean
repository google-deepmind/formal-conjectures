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

# Erdős Problem 354
*References:*
- [erdosproblems.com/354](https://www.erdosproblems.com/354)
- [YC26] Yingzhe Yu and Kani Chen, *Erdős Problem 354(i): Strong Completeness of Two
  Dyadic Floor Sequences* (2026).
  [Manuscript](https://github.com/Andrewyzzz/erdos354/blob/c735d9389a79a2aa20fc04103d8890dd330b531e/proof/FORMALIZED_PROOF.pdf)

-/

@[expose] public section
namespace Erdos354

/-- The sequence `⌊a⌋, ⌊γ * a⌋, ⌊γ ^ 2 * a⌋, ..., ⌊γ ^ i * a⌋, ...`. -/
noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

/-- The sequence `⌊a⌋, ⌊b⌋, ⌊γ * a⌋, ⌊γ * b⌋, ... ⌊γ ^ i * a⌋, ⌊γ ^ i * b⌋, ...` -/
noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    FloorMultiples a γ (n / 2)
  else
    FloorMultiples b γ (n / 2)

/-- Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is the multiset
$$\{ \lfloor \alpha\rfloor,\lfloor 2\alpha\rfloor,\lfloor 4\alpha\rfloor,\ldots\}\cup
\{ \lfloor \beta\rfloor,\lfloor 2\beta\rfloor,\lfloor 4\beta\rfloor,\ldots\}$$ complete?

Yu and Chen [YC26] prove an affirmative answer. They also prove that the set of nonzero
values remains complete after deletion of any finite set of values.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/Andrewyzzz/erdos354/blob/c735d9389a79a2aa20fc04103d8890dd330b531e/formalization/Dyadic354/UpstreamBridge.lean#L34"]
theorem erdos_354.parts.i : answer(True) ↔ ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2) := by
  sorry

/-- Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is
$$\{ \lfloor \alpha\rfloor,\lfloor \gamma\alpha\rfloor,\lfloor \gamma^2\alpha\rfloor,\ldots\}\cup
\{ \lfloor \beta\rfloor,\lfloor \gamma\beta\rfloor,\lfloor \gamma^2\beta\rfloor,\ldots\}$$ complete? -/
@[category research open, AMS 11]
theorem erdos_354.parts.ii : answer(sorry) ↔ ∃ γ ∈ Set.Ioo (1 : ℝ) 2, ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddCompleteNatSeq' (FloorMultiples.interleave α β γ) := by
  sorry

end Erdos354
