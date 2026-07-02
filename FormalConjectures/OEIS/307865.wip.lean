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
# Conjectures associated with A307865

A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$.
We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.

A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.

*References:*
- [A307865](https://oeis.org/A307865)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA307865


open Nat Finset ZMod

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$.
We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)


@[category test, AMS 11]
lemma a_zero : a 0 = 0 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 0 := by rfl


/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$.
We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.

A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/307865.wip.lean#L190"]
theorem target_theorem_0
  (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
    sorry

end OeisA307865
