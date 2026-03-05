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
# Erdős Problem 393

*Reference:* [erdosproblems.com/393](https://www.erdosproblems.com/393)

Let $f(n)$ denote the minimal $m \geq 1$ such that $n! = a_1 \cdots a_t$ with
$a_1 < \cdots < a_t = a_1 + m$. What is the behaviour of $f(n)$?

Erdős and Graham write that they do not even know whether $f(n) = 1$ infinitely
often (i.e. whether a factorial is the product of consecutive integers infinitely
often).

A result of Luca implies that $f(n) \to \infty$ as $n \to \infty$, conditional
on the ABC conjecture.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in
combinatorial number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Filter

namespace Erdos393

/-- A factorization of $n!$ as a product of distinct positive integers whose
maximum minus minimum equals $m$. Concretely, there is a finite set of
positive integers all contained in $[a, a + m]$ (with both $a$ and $a + m$
achieved) whose product is $n!$. -/
def HasFactorizationWithSpread (n m : ℕ) : Prop :=
  ∃ (s : Finset ℕ),
    2 ≤ s.card ∧
    (∀ x ∈ s, 0 < x) ∧
    s.prod id = n.factorial ∧
    ∃ a ∈ s, a + m ∈ s ∧ ∀ x ∈ s, a ≤ x ∧ x ≤ a + m

/-- The minimal $m \geq 1$ such that $n!$ can be written as a product of distinct
positive integers spanning a range of exactly $m$. Returns $0$ if no such
factorization exists (e.g. for $n \leq 1$). -/
noncomputable def erdos393_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ HasFactorizationWithSpread n m}

/--
Erdős Problem 393 [ErGr80, p.76]:

$f(n) \to \infty$ as $n \to \infty$, where $f(n)$ is the minimum spread of any
factorization of $n!$ into distinct positive integers. Implied by the ABC conjecture
via a result of Luca.
-/
@[category research open, AMS 11]
theorem erdos_393 :
    Tendsto (fun n : ℕ => erdos393_f n) atTop atTop := by
  sorry

end Erdos393
