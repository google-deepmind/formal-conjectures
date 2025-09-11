/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/409
import FormalConjectures.Util.ProblemImports

open scoped Topology ArithmeticFunction

/--
How many iterations of $n\mapsto\phi(n) + 1$ are needed before a prime is reached?
-/
@[problem_status open]
theorem erdos_409.parts.i (n : ℕ) :
    IsLeast { i | (fun j => j.totient + 1)^[i] n |>.Prime } answer(sorry) :=
  sorry

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[problem_status open]
theorem erdos_409.parts.ii
    (iterEnd : ℕ → ℕ)
    (iterEnd_spec: ∀ n, IsLeast { i | (fun j => j.totient + 1)^[i] n |>.Prime } (iterEnd n)) :
    ∃ (p : ℕ) (hp : p.Prime),
      { n | (fun j => j.totient + 1)^[iterEnd n] n = p }.Infinite :=
  sorry

/--
What is the density of $n$ which reach any fixed prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[problem_status open]
theorem erdos_409.parts.iii (p : ℕ)
    (h : p.Prime)
    (iterEnd : ℕ → ℕ)
    (iterEnd_spec: ∀ n, IsLeast { i | (fun j => j.totient + 1)^[i] n |>.Prime } (iterEnd n))
    (α : ℝ)
    (hα : { n | (fun j => j.totient + 1)^[iterEnd n] n = p }.HasDensity α) :
    α = answer(sorry) :=
  sorry

/--
How many iterations of $n\mapsto\sigma(n) - 1$ are needed before a prime is reached?
-/
@[problem_status open]
theorem erdos_409.variants.sigma.parts.i (n : ℕ) :
    IsLeast { i | (fun j => (σ 1 j - 1 : ℕ))^[i] n |>.Prime } answer(sorry) :=
  sorry

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\sigma(n) - 1$?
-/
@[problem_status open]
theorem erdos_409.variants.sigma.parts.ii
    (iterEnd : ℕ → ℕ)
    (iterEnd_spec: ∀ n, IsLeast { i | (fun j => (σ 1 j - 1 : ℕ))^[i] n |>.Prime } (iterEnd n)) :
    ∃ (p : ℕ) (hp : p.Prime),
      { n | (fun j => (j.totient - 1 : ℕ))^[iterEnd n] n = p }.Infinite :=
  sorry

/--
What is the density of $n$ which reach any fixed prime under the iteration $n\mapsto\sigma(n) - 1$?
-/
@[problem_status open]
theorem erdos_409.variants.sigma.parts.iii (p : ℕ)
    (h : p.Prime)
    (iterEnd : ℕ → ℕ)
    (iterEnd_spec: ∀ n, IsLeast { i | (fun j => (σ 1 j - 1 : ℕ))^[i] n |>.Prime } (iterEnd n))
    (α : ℝ)
    (hα : { n | (fun j => (j.totient - 1 : ℕ))^[iterEnd n] n = p }.HasDensity α) :
    α = answer(sorry) :=
  sorry
