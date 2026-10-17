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
# Erdős Problem 271

*References:*
- [erdosproblems.com/271](https://www.erdosproblems.com/271)
- [Mo11] Moy, Richard A., *On the growth of the counting function of Stanley sequences*.
  Discrete Math. (2011), 560–562. [arXiv](https://arxiv.org/abs/1101.0022v3).
- [Explicit bound in the comments](https://www.erdosproblems.com/forum/thread/271).
-/

@[expose] public section

namespace Erdos271

open StanleySequence

/-- van Doorn and Sothanaphan have noted in the comment section that Moy's proof can be
upgraded to give a fully explicit result of $a_k\leq \frac{(k-1)(k+2)}{2}+n$ for all $k\geq 0$.
Here $n>0$ and the sequence has seed $a_0=0$, $a_1=n$. -/
@[category research solved, AMS 5 11]
theorem erdos_271.variants.explicit_bound {n : ℕ} (hn : 0 < n)
    {b : ℕ → ℕ} (hb : IsStanley n b) (k : ℕ) :
    (b k : ℝ) ≤ (n : ℝ) + ((k : ℝ) - 1) * ((k : ℝ) + 2) / 2 := by
  exact explicit_bound_of_isStanley hn hb k

end Erdos271