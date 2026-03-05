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
# Erdős Problem 408

*Reference:* [erdosproblems.com/408](https://www.erdosproblems.com/408)

Let $f(n)$ be the number of iterations of Euler's totient function needed to reach $1$.
Is it true that $f(n)/\log(n)$ has a distribution function, and that $f(n)/\log(n)$
concentrates around a constant $\alpha$ (expected to be $1/\log 2$)?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[EGPS90] Erdős, P., Granville, A., Pomerance, C., and Spiro, C., *On the normal behavior
of the iterates of some arithmetic functions*. Analytic Number Theory (1990), 165–204.
-/

open Filter Finset

namespace Erdos408

/--
The $k$-fold iteration of Euler's totient function.
Applies $\varphi$ to $n$ exactly $k$ times: $\varphi^{[0]}(n) = n$,
$\varphi^{[k]}(n) = \varphi(\varphi^{[k-1]}(n))$.
-/
def iteratedTotient (k n : ℕ) : ℕ := Nat.totient^[k] n

/-- The iterated totient function eventually reaches $1$ for any $n \ge 2$,
since $\varphi(m) < m$ for $m \ge 2$ and $\varphi(1) = 1$. -/
@[category test, AMS 11]
lemma iteratedTotient_reaches_one {n : ℕ} (hn : 1 < n) :
    ∃ k, iteratedTotient k n = 1 := by
  sorry

/--
$f(n) = \min\{k : \varphi^{[k]}(n) = 1\}$, the number of iterations of Euler's totient
function needed to reach $1$. Returns $0$ for $n \le 1$.
This is well-defined for $n \ge 2$ since $\varphi(m) < m$ for $m \ge 2$ and $\varphi(1) = 1$.
-/
noncomputable def totientIterationLength (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else Nat.find (iteratedTotient_reaches_one (not_le.mp h))

/--
Erdős Problem 408 [ErGr80] — Part (a).

Let $\varphi(n)$ be the Euler totient function and $\varphi_k(n)$ be the $k$-fold iterate
of $\varphi$, so that $\varphi_1(n) = \varphi(n)$ and
$\varphi_k(n) = \varphi(\varphi_{k-1}(n))$. Let $f(n) = \min\{k : \varphi_k(n) = 1\}$.

$f(n)/\log(n)$ has a distribution function, i.e., for every real $c$, the natural density
of $\{n \le N : f(n)/\log(n) \le c\}$ exists.

Erdős, Granville, Pomerance, and Spiro [EGPS90] proved this conditional on a form of the
Elliott–Halberstam conjecture.
-/
@[category research open, AMS 11]
theorem erdos_408 :
    ∀ c : ℝ,
      ∃ d : ℝ, Tendsto
        (fun N : ℕ =>
          (((range N).filter (fun n =>
            (totientIterationLength n : ℝ) / Real.log n ≤ c)).card : ℝ) / (N : ℝ))
        atTop (nhds d) := by
  sorry

/--
Erdős Problem 408 [ErGr80] — Part (b).

$f(n)/\log(n)$ is almost always equal to some constant $\alpha > 0$, i.e., there exists
$\alpha > 0$ such that for all $\varepsilon > 0$, the natural density of
$\{n : |f(n)/\log(n) - \alpha| \ge \varepsilon\}$ is zero.

It is expected that $\alpha = 1/\log(2)$. Erdős, Granville, Pomerance, and Spiro [EGPS90]
proved this conditional on a form of the Elliott–Halberstam conjecture.
-/
@[category research open, AMS 11]
theorem erdos_408.variants.concentration :
    ∃ α : ℝ, α > 0 ∧
      ∀ ε : ℝ, ε > 0 →
        Tendsto
          (fun N : ℕ =>
            (((range N).filter (fun n =>
              ε ≤ |((totientIterationLength n : ℝ) / Real.log n) - α|)).card : ℝ) / (N : ℝ))
          atTop (nhds 0) := by
  sorry

end Erdos408
