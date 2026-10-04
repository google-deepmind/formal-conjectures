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
public import FormalConjecturesForMathlib.NumberTheory.UnitFractionGap

/-!
# Erdős Problem 311

*Reference:* [erdosproblems.com/311](https://www.erdosproblems.com/311)

The supporting module defines the minimum nonzero reciprocal-sum gap and relates
the website and Erdős–Graham formulations.
-/

@[expose] public section

namespace Erdos311

/--
Let $\delta(N)$ be the smallest nonzero value of $|1 - \sum_{n \in A} 1/n|$ over
subsets $A \subseteq \{1, \ldots, N\}$. Is
$\delta(N) = e^{-(c + o(1))N}$ for some $c \in (0,1)$?
-/
@[category research open, AMS 11]
theorem erdos_311 : answer(sorry) ↔ Erdos311Conjecture := by
  sorry

end Erdos311
