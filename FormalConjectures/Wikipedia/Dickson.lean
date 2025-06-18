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
open Polynomial

/-!
# Dickson's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dickson%27s_conjecture)
- [Arxiv](https://arxiv.org/pdf/0906.3850)
-/

/--
**Dickson's conjecture**
If a finite set of in linear integer forms $f_i(n) = a_i n+b_i$ satisfies Schinzel condition,
there exist infinitely many natural numbers $m$ such that $f_i(m)$ are primes for all $i$.
-/
@[category research open, AMS 11]
theorem dickson_conjecture (fs : Finset ℤ[X]) (hfs : ∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) 
    (hfs' : SchinzelCondition fs) : Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime} := by
  sorry

/-! ## Special cases -/

/--
**Polignac's conjecture**
For any integer $k$ there are infinitely many primes $p$ such that $p + 2k$ is prime.
-/
@[category research open, AMS 11]
theorem polignac_conjecture (k : ℕ) :
    Infinite {p : ℕ | p.Prime ∧ (p + 2 * k).Prime} := by
  sorry

/--
**The infinitude of Sophie Germain primes**
There are infinitely many primes $p$ such that $2p + 1$ is prime.
-/
@[category research open, AMS 11]
theorem infinite_safe_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (2 * p + 1)} := by
  sorry

/--
**The infinitude of cousin primes**
There are infinitely many primes $p$ such that $p + 4$ is prime.
-/
@[category research open, AMS 11]
theorem infinite_cousin_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 4)} := by
  sorry

/--
**The infinitude of sexy primes**
There are infinitely many primes $p$ such that $p + 6$ is prime.
-/
@[category research open, AMS 11]
theorem infinite_sexy_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 6)} := by
  sorry

/-
## Other consequences
- Landau's fourth problem (primes and perfect squares)
- Twin prime conjecture
- Artin's primitive root conjecture
- First Hardy–Littlewood conjecture

*Reference:* [Arxiv](https://arxiv.org/pdf/0906.3850)
-/
