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
# Erdős Problem 852

*References:*
- [erdosproblems.com/852](https://www.erdosproblems.com/852)
- [Er85c] Erdős, P., *On some of my problems in number theory I would most like to see solved*.
  Number theory (Ootacamund, 1984) (1985), 74-84.
- [A001223](https://oeis.org/A001223)
- [A053597](https://oeis.org/A053597)
- [A078515](https://oeis.org/A078515)
-/

@[expose] public section

open Filter

namespace Erdos852

/-- The $H$ prime gaps $d_n, d_{n+1}, \ldots, d_{n+H-1}$ are pairwise distinct.

Here $d_n = p_{n+1} - p_n$ is `primeGap n`, so the primes are indexed from $p_0 = 2$. The empty run
$H = 0$ and every run with $H = 1$ are distinct. -/
def DistinctGapRun (n H : ℕ) : Prop :=
  Set.InjOn primeGap (Set.Ico n (n + H))

/-- The gaps $d_0, d_1 = 1, 2$ are distinct. -/
@[category test, AMS 11]
theorem distinctGapRun_zero_two : DistinctGapRun 0 2 := by
  have h0 : primeGap 0 = 1 := by simp [primeGap]
  have h1 : primeGap 1 = 2 := by simp [primeGap]
  intro a ha b hb hab
  simp only [Set.mem_Ico] at ha hb
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> omega

/-- The gaps $d_0, d_1, d_2 = 1, 2, 2$ are not distinct. -/
@[category test, AMS 11]
theorem not_distinctGapRun_zero_three : ¬ DistinctGapRun 0 3 := by
  have h1 : primeGap 1 = 2 := by simp [primeGap]
  have h2 : primeGap 2 = 2 := by simp [primeGap]
  intro h
  have := h (show (1 : ℕ) ∈ Set.Ico 0 (0 + 3) by simp) (show (2 : ℕ) ∈ Set.Ico 0 (0 + 3) by simp)
    (h1.trans h2.symm)
  omega

/--
Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$th prime. Let $h(x)$ be maximal such that for
some $n < x$ the numbers $d_n, d_{n+1}, \ldots, d_{n+h(x)-1}$ are all distinct [Er85c]. Estimate
$h(x)$. In particular, is it true that
$$h(x) > (\log x)^c$$
for some constant $c > 0$?

The statement avoids defining $h$. Since $h(x)$ is the longest such run, $h(x) > y$ holds exactly
when some $n < x$ starts a run of $H > y$ distinct gaps. We state the question this way, with $x$
real. We read it as asking for one $c > 0$ such that the inequality holds for all large $x$.

The primes are indexed from $p_0 = 2$, as in `primeGap`. Shifting the index by one does not change
the question.
-/
@[category research open, AMS 11]
theorem erdos_852.parts.i : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∃ n : ℕ, (n : ℝ) < x ∧ ∃ H : ℕ, (Real.log x) ^ c < (H : ℝ) ∧ DistinctGapRun n H := by
  sorry

/--
Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$th prime. Let $h(x)$ be maximal such that for
some $n < x$ the numbers $d_n, d_{n+1}, \ldots, d_{n+h(x)-1}$ are all distinct [Er85c]. Estimate
$h(x)$. In particular, is it true that
$$h(x) = o(\log x)?$$

The statement avoids defining $h$. It says that for every $\varepsilon > 0$ and all large real $x$,
every run of $H$ distinct gaps $d_n, \ldots, d_{n+H-1}$ with $n < x$ satisfies
$H \leq \varepsilon \log x$. This is $h(x) \leq \varepsilon \log x$, because $h(x)$ is the longest
such run.

The indexing is as in `Erdos852.erdos_852.parts.i`.
-/
@[category research open, AMS 11]
theorem erdos_852.parts.ii : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ, (n : ℝ) < x → ∀ H : ℕ, DistinctGapRun n H → (H : ℝ) ≤ ε * Real.log x := by
  sorry

/--
Brun's sieve implies $h(x) \to \infty$ as $x \to \infty$ (remark on
[erdosproblems.com/852](https://www.erdosproblems.com/852)).

That is, for every $H$ and all large $x$ there is some $n < x$ such that $d_n, \ldots, d_{n+H-1}$
are all distinct. Since more values of $n$ are allowed as $x$ grows, this holds exactly when, for
every $H$, some $n$ has $d_n, \ldots, d_{n+H-1}$ all distinct.

This also follows from `Erdos6.erdos_6.variants.increasing`, because strictly increasing prime
gaps are distinct.
-/
@[category research solved, AMS 11]
theorem erdos_852.variants.tendsto_atTop :
    ∀ H : ℕ, ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, (n : ℝ) < x ∧ DistinctGapRun n H := by
  sorry

end Erdos852
