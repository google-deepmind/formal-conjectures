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

public import FormalConjecturesForMathlib.Data.Nat.Prime.Composite

@[expose] public section

/-!
# Riesel numbers

*References:*
- [Wikipedia, Riesel number](https://en.wikipedia.org/wiki/Riesel_number)
- [Ri56] Riesel, H., Några stora primtal. Elementa 39 (1956), 258–260.

A positive odd integer $k$ is a *Riesel number* if $k \cdot 2^n - 1$ is composite for all
natural numbers $n$.
-/

namespace Nat

/--
A positive odd integer $k$ is a
[Riesel number](https://en.wikipedia.org/wiki/Riesel_number) if $k \cdot 2^n - 1$
is composite for all natural numbers $n$. In other words, every member of the set
$\{k \cdot 2^n - 1 : n \in \mathbb{N}\}$ is composite.
-/
def IsRieselNumber (k : ℕ) : Prop :=
  ¬ 2 ∣ k ∧ ∀ n, (k * 2 ^ n - 1).Composite

end Nat

