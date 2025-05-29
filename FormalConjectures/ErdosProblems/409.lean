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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 409

*Reference:* [erdosproblems.com/409](https://www.erdosproblems.com/409)
-/
open scoped Topology ArithmeticFunction Nat
open Filter

/--
How many iterations of $n\mapsto\phi(n) + 1$ are needed before a prime is reached?
-/
-- Formalisation note: the sequence of iterates always terminates if `n > 0`
-- since it is strictly decreasing unless the input is prime, at which point
-- it becomes static. See also https://oeis.org/A039651
@[category research open, AMS 11]
theorem erdos_409.parts.i (n : ℕ) (hn : 0 < n) :
    IsLeast { i | (φ · + 1)^[i] n |>.Prime } answer(sorry) :=
  sorry

/-- If $n > 0$, then the iteration $n\mapsto\phi(n) + 1$ necessarily
reaches a prime. -/
@[category test]
theorem erdos_409.termination (n : ℕ) (hn : 0 < n) :
    ∃ i, (φ · + 1)^[i] n |>.Prime :=
  sorry

-- Formalisation note: it's possible that solution to `erdos_409.parts.i` needs to be
-- expressed asymptotically. To handle this we include `IsTheta`, `IsBigO`
-- and `IsLittleO` variants below. Since a solution is not known this necessitates
-- the use of an `answer(sorry)` placeholder. Trivial or sub-optimal solutions
-- will therefore exist to the asymptotic formalisations. A true solution to
-- the asymptotic variants should have a degree of optimality or non-triviality to it.
/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. What is $\Theta(c(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.variants.isTheta (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = O(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.variants.isBigO (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = o(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.variants.isLittleO (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.ii :
    ∃ (p : ℕ) (hp : p.Prime), { n | ∃ i, (φ · + 1)^[i] n = p }.Infinite :=
  sorry

/--
What is the density of $n$ which reach any fixed prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.iii (p : ℕ) (h : p.Prime) (α : ℝ)
    (hα : { n | ∃ i, (φ · + 1)^[i] n = p }.HasDensity α) :
    α = answer(sorry) :=
  sorry

/--
How many iterations of $n\mapsto\sigma(n) - 1$ are needed before a prime is reached?
-/
-- Formalisation note: non-termination of this sequence is less clear since
-- it is strictly increasing except at primes.
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.i (n : ℕ) (hn : n > 1) :
    IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } answer(sorry) :=
  sorry

/-- If $n > 1$ then the iteration $n\mapsto\sigma(n) - 1$ necessarily reaches a prime. -/
@[category test]
theorem erdos_409.variants.sigma.termination (n : ℕ) (hn : n > 1) :
    ∃ i, (σ 1 · - 1)^[i] n |>.Prime :=
  sorry

-- Formalisation note: See the above formalisation note for the rationale
-- for including asymptotic variants
/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. What is $\Theta(c(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.i.isTheta (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = O(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.i.isBigO (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = o(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.i.isLittleO (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) :=
  sorry

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\sigma(n) - 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.ii :
    ∃ (p : ℕ) (hp : p.Prime), { n | ∃ i, (σ 1 · - 1)^[i] n = p }.Infinite :=
  sorry

/--
What is the density of $n$ which reach any fixed prime under the iteration $n\mapsto\sigma(n) - 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma.parts.iii (p : ℕ) (h : p.Prime) (α : ℝ)
    (hα : { n | ∃ i, (σ 1 · - 1)^[i] n = p }.HasDensity α) :
    α = answer(sorry) :=
  sorry
