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

import FormalConjecturesUtil

/-!
# Erdős Problem 907

*References:*
- [erdosproblems.com/907](https://www.erdosproblems.com/907)
- [dB51] de Bruijn, N. G., *Functions whose differences belong to a given class*. Nieuw Arch.
  Wiskunde (2) (1951), 194-218.
-/

namespace Erdos907

/--
Let $f:\mathbb{R}\to \mathbb{R}$ be such that $f(x+h)-f(x)$ is continuous for every $h>0$. Is it
true that
\[f=g+h\]
for some continuous $g$ and additive $h$ (i.e. $h(x+y)=h(x)+h(y)$)?

A conjecture of Erdős from the early 1950s. Answered in the affirmative by de Bruijn [dB51].
-/
@[category research solved, AMS 26 39]
theorem erdos_907 : answer(True) ↔
    ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) →
      ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧ f = g + a := by
  sorry

end Erdos907
