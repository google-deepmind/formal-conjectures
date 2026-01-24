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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 120

*Reference:*
- [erdosproblems.com/120](https://www.erdosproblems.com/120)
- [St20](http://matwbn.icm.edu.pl/ksiazki/fm/fm1/fm1111.pdf) Steinhaus, Hugo, Sur les distances des points dans les ensembles de measure positive. Fund. Math. (1920), 93-104.
-/

open Set MeasureTheory

namespace Erdos120

/--
There exists a set $E \subseteq \mathbb{R}$, dependent on set $A \subseteq \mathbb{R}$,
of positive measure which does not contain any set of the shape $a * A + b$
for some $a,b \in \mathbb{R}$ and $a \neq 0$?
-/
def Erdos120For (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  0 < volume E ∧ ∀ a b : ℝ, a ≠ 0 ∧ ¬ .image (fun x => a * x + b) A ⊆ E

/--
Let $A \subseteq \mathbb{R}$ be an infinite set. Must there be a set $E \subseteq \mathbb{R}$
of positive measure which does not contain any set of the shape $a * A + b$
for some $a,b \in \mathbb{R}$ and $a \neq 0$?
-/
@[category research open, AMS 05 28]
theorem erdos_120 : answer(sorry) ↔ ∀ A : Set ℝ, A.Infinite → Erdos120For A := by
  sorry

/--
Steinhaus [St20] has proved Erdős 120 to be false whenever $A$ is a finite set.
-/
@[category research solved, AMS 05 28]
theorem erdos_120.variants.finite_set {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  sorry

end Erdos120
