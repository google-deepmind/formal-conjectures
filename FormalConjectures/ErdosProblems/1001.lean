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

public import FormalConjecturesUtil

/-!
# Erdős Problem 1001

*References:*
- [erdosproblems.com/1001](https://www.erdosproblems.com/1001)
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math.
  16 (1964), 52-65. [PDF](https://www.numdam.org/item/CM_1964__16__52_0.pdf)
- [EST58] Erdős, P. and Szüsz, P. and Turán, P., *Remarks on the theory of diophantine
  approximation*. Colloq. Math. 6 (1958), 119-126.
- [KeSo66] Kesten, H. and Sós, V. T., *On two problems of Erdős, Szüsz and Turán concerning
  diophantine approximations*. Acta Arith. 12 (1966/67), 183-192.
- [XiZa06] Xiong, Maosheng and Zaharescu, Alexandru, *A problem of Erdős-Szüsz-Turán on
  diophantine approximation*. Acta Arith. 125 (2006), 163-177.
- [Bo08] Boca, Florin P., *A problem of Erdős, Szüsz and Turán concerning Diophantine
  approximations*. Int. J. Number Theory 4 (2008), 691-708.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace Erdos1001

/--
The set of $\alpha\in(0,1)$ such that $\lvert\alpha-x/y\rvert<A/y^2$ for some integer $x$ and
some natural number $y$ with $N\le y\le cN$ and $(x,y)=1$. The condition $(x,y)=1$ is
`x.natAbs.Coprime y`.
-/
noncomputable def approximableSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α | α ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ x : ℤ, ∃ y : ℕ, 0 < y ∧ N ≤ y ∧ (y : ℝ) ≤ c * (N : ℝ) ∧ x.natAbs.Coprime y ∧
      |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2}

/--
$S(N,A,c)$: the Lebesgue measure of `approximableSet N A c`. This set lies in $(0,1)$, so its
measure is finite and `Measure.real` has no junk value. For $A\le 0$ or $c<1$ the set is empty
and $S=0$.
-/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ :=
  volume.real (approximableSet N A c)

/--
Let $S(N,A,c)$ be the measure of the set of those $\alpha\in (0,1)$ such that
$$\left\lvert \alpha-\frac{x}{y}\right\rvert< \frac{A}{y^2}$$
for some $N\leq y\leq cN$ and $(x,y)=1$. Does
$$\lim_{N\to \infty}S(N,A,c)=f(A,c)$$
exist?

This is a problem of Erdős, Szüsz, and Turán [EST58], restated in [Er64b, p. 62]. The existence
of the limit for all $A>0$ and $c\geq 1$ was proved by Kesten and Sós [KeSo66]. Boca [Bo08] and
Xiong and Zaharescu [XiZa06, Theorem 2] gave further proofs. We assume $A>0$ and $c\geq 1$,
since otherwise $S=0$. The second question, the explicit form of $f(A,c)$, is not stated here.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1001.lean#L8077"]
theorem erdos_1001.parts.i (A c : ℝ) (hA : 0 < A) (hc : 1 ≤ c) :
    ∃ f : ℝ, Tendsto (fun N : ℕ ↦ S N A c) atTop (𝓝 f) := by
  sorry

/--
Erdős, Szüsz, and Turán [EST58] proved that
$$f(A,c)=\frac{12 A\log c}{\pi^2}$$
when $0<A< \frac{c}{1+c^2}$. Here $c\geq 1$, since the range $N\leq y\leq cN$ is empty for
$c<1$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1001.lean#L1047"]
theorem erdos_1001.variants.est_formula (A c : ℝ) (hA : 0 < A) (hc : 1 ≤ c)
    (hAc : A < c / (1 + c ^ 2)) :
    Tendsto (fun N : ℕ ↦ S N A c) atTop (𝓝 (12 * A * Real.log c / Real.pi ^ 2)) := by
  sorry

end Erdos1001
