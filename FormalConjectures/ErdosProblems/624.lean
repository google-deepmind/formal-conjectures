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
# Erdős Problem 624

*Reference:* [erdosproblems.com/624](https://www.erdosproblems.com/624)
-/
open Filter

open scoped Topology Finset

/-- Structure encoding functions on finite sets that map the powerset of the
supplied finite set `X` to `X`. -/
structure PowersetMapFor {α : Type*} (X : Finset α) where
  toFun : Finset α → α
  image : toFun '' X.powerset ⊆ X

instance {α : Type*} (X : Finset α) : FunLike (PowersetMapFor X) (Finset α) α where
  coe := PowersetMapFor.toFun
  coe_injective' f₁ _ _ := by cases f₁; congr

/-- Structure encoding functions on finite sets that, for any finite set `X`,
map the powerset of `X` to `X`. -/
structure PowersetMap (α : Type*) where
  toFun : Finset α → Finset α → α
  image : ∀ X, toFun X '' X.powerset ⊆ X

instance {α : Type*} : FunLike (PowersetMap α) (Finset α) (Finset α → α) where
  coe := PowersetMap.toFun
  coe_injective' f₁ _ _ := by cases f₁; congr

/-- `f : PowersetMap` is `SurjectiveAbove` a function `H : ℕ → ℕ` if its
image on the powerset of `Y` is `X` for any `X Y` such that `H #X ≤ #Y`. -/
def PowersetMap.SurjectiveAbove {α : Type*} (H : ℕ → ℕ)
    (f : PowersetMap α) : Prop :=
  ∀ X Y, Y ⊆ X → H #X ≤ #Y → Set.SurjOn (f X) Y.powerset X

/--
Let $X$ be a finite set of size $n$ and $H(n)$ be such that there
is a function $f : \{A : A \subseteq X\} \to X$ so that for every
$Y \subseteq X$ with $|Y|\geq H(n)$ we have
$$
  \{f(A) : A \subseteq Y\} = X.
$$
Prove that
$$
  H(n) - \log_2 n \to\infty.
$$
-/
@[category research open, AMS 5]
theorem erdos_624 {α : Type*} {H : ℕ → ℕ} {f : PowersetMap α}
    (hf : f.SurjectiveAbove H) :
    Tendsto (fun n => H n - Real.logb 2 n) atTop atTop :=
  sorry

open Real in
/--
Erdős and Hajnal proved that
$$
  \log_2 n\leq H(n) < \log_2 n + (3 + o(1))\log_2\log_2 n.
$$
-/
@[category research solved, AMS 5]
theorem erdos_624.variants.interval {α : Type*} {H : ℕ → ℕ} {f : PowersetMap α}
    (hf : f.SurjectiveAbove H) :
    ∃ (o : ℕ → ℕ) (ho : (fun n => (o n : ℝ)) =o[atTop] (1 : ℕ → ℝ)), ∀ (n : ℕ),
        logb 2 n ≤ H n ∧ H n < logb 2 n + (3 + o n) * logb 2 (logb 2 n) :=
  sorry

/--
The weaker statement that for $n = 2 ^ k$ we have $H(n)\geq k + 1$ was
proved by Alon.
-/
@[category undergraduate, AMS 5]
theorem erdos_624.variants.pow_two_weak {α : Type*} {H : ℕ → ℕ}
    {f : PowersetMap α} (hf : f.SurjectiveAbove H) (n : ℕ) (h : n.isPowerOfTwo) :
    h.choose + 1 ≤ H n :=
  sorry

/--
Erdős and Gyárfás conjectured that if $|X| = 2^k$ then, for any
$f : \{A : A \subseteq X\} \to X$, there must exist some $Y \subset X$
of size $k$ such that
$$
  \#\{f(A) : A \subseteq Y\}< 2^k - k ^ C
$$
for every $C$ (with $k$ sufficiently large depending on $C$)
was proved by Alon.
-/
@[category research solved, AMS 5]
theorem erdos_624.variants.pow_two_strong {α : Type*} (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k in atTop, ∀ (X : Finset α) (hX : #X = 2 ^ k) (f : PowersetMapFor X),
      ∃ Y ⊆ X, #Y = k ∧ { f A | A ⊆ Y }.ncard < 2 ^ k - (k : ℝ) ^ C :=
  sorry

/--
Alon proved Erdős' and Gyárfás' conjecture via the stronger version that,
for any $\epsilon > 0$, if $k$ is large enough, there must exists some $Y$ of
size $k$ such that
$$
  \#\{f(A) : A \subseteq Y\} < (1 - \epsilon)2^k.
$$
-/
@[category research solved, AMS 5]
theorem erdos_624.variants.pow_two_stronger {α : Type*} (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (X : Finset α) (hX : X.card = 2 ^ k) (f : PowersetMapFor X),
      ∃ Y ⊆ X, Y.card = k ∧ { f A | A ⊆ Y }.ncard < (1 - ε) * 2 ^ k :=
  sorry

/--
Alon also proved that, provided $k$ is large enough, if $|X| = 2^k$
there exists some $f : \{A : A\subseteq X\} \to X$ such that,
if $Y\subset X$ with $|Y| = k$, then
$$
  \#\{f(A) : A\subseteq Y\} > \tfrac{1}{4}2^k.
$$
-/
@[category research solved, AMS 5]
theorem erdos_624.variants.pow_two_lb {α : Type*} :
    ∀ᶠ k in atTop, ∀ (X : Finset α) (hX : X.card = 2 ^ k),
      ∃ (f : PowersetMapFor X),
        ∀ Y ⊆ X, Y.card = k ∧ 2 ^ k < 4 * { f A | A ⊆ Y }.ncard :=
  sorry
