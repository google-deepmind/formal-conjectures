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
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Amicable numbers

Two natural numbers $a$ and $b$ are amicable if $\sigma(a) = \sigma(b) = a + b$,
where $\sigma$ is the sum-of-divisors function.
-/

open scoped ArithmeticFunction

/--
We say that $a,b\in \mathbb{N}$ are an amicable pair if $\sigma(a)=\sigma(b)=a+b$.
-/
@[mk_iff]
structure IsAmicable (a b : ℕ) : Prop where
  left : σ 1 a = a + b
  right : σ 1 b = a + b
