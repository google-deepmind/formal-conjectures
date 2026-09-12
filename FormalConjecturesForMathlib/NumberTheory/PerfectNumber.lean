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

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

open scoped ArithmeticFunction.sigma

namespace Nat

/--
A positive integer $n$ is $(m,k)$-perfect if $\sigma^m(n) = kn$, where $\sigma^m$ is
the $m$-th iterate of the sum-of-divisors function $\sigma$.
-/
def IsPerfectFor (n m k : ℕ) : Prop :=
  0 < n ∧ Nat.iterate (fun x => σ 1 x) m n = k * n

end Nat
