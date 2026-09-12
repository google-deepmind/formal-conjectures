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
# Erdős Problem 963

*References:*
- [erdosproblems.com/963](https://www.erdosproblems.com/963)
- [Er65] Erdős, P., Extremal problems in number theory. Proc. Sympos. Pure Math., Vol. VIII (1965), 181-189.
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

namespace Erdos963

/--
A finite set of reals is dissociated if the subset sums $\sum_{b\in S}b$ are distinct for all
subsets $S$.
-/
def IsDissociated (B : Finset ℝ) : Prop :=
  (B.powerset : Set (Finset ℝ)).InjOn fun S ↦ ∑ x ∈ S, x

/--
`HasDissociatedSubset n k` means that every set of `n` reals has a dissociated subset of size
at least `k`.
-/
def HasDissociatedSubset (n k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, k ≤ B.card ∧ IsDissociated B

/--
The maximal $k$ such that every real set of size $n$ has a dissociated subset of size at least $k$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => HasDissociatedSubset n k) n

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated that is, the sums $\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Estimate $f(n)$ - in particular, is it true that
$$f(n)\geq \lfloor \log_2 n\rfloor?$$
-/
@[category research open, AMS 5 11]
theorem erdos_963 :
    answer(sorry) ↔ ∀ n, Nat.log 2 n ≤ f n := by
  sorry

/--
Erdős noted that the greedy algorithm showed $f(n)\geq \lfloor \log_3 n\rfloor$.
-/
@[category research solved, AMS 5 11]
theorem erdos_963.variants.greedy :
    ∀ n, Nat.log 3 n ≤ f n := by
  sorry

end Erdos963
