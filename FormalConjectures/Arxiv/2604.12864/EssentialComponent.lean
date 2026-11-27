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
# $d$-essential components of full upper density

*Reference:* [arXiv:2604.12864v1](https://arxiv.org/abs/2604.12864v1)
**An inverse theorem for sumsets of sets of positive density in the integers**
by *Ethan Ackelsberg, Florian K. Richter* (2026)

The paper works in $\mathbb{N} = \{1, 2, 3, \ldots\}$ with the lower density
$\underline{d}(A) = \liminf_{N \to \infty} |A \cap [N]| / N$, the upper density
$\overline{d}(A)$ (the $\limsup$), and the density $d(A)$ when the two agree.
Section 16 asks whether every set of full upper density is a $d$-essential component.

* **In-Paper Location:** Question 16.9, Section 16
-/

@[expose] public section

open scoped Pointwise

namespace Arxiv.«2604.12864»

/--
A set $B \subseteq \mathbb{N}$ is a *$d$-essential component* if
$\underline{d}(A + B) > d(A)$ for every $A \subseteq \mathbb{N}$ whose density $d(A)$ exists and
lies in $(0, 1)$.

The paper's $\mathbb{N}$ starts at $1$, so `A` must avoid `0` here. Allowing $0 \in A$ would put
$B$ itself inside $A + B$. The densities on `Set ℕ` count the elements below `b`, including `0`.
For sets that avoid `0` they agree with the paper's densities, which count in
$[N] = \{1, \ldots, N\}$.
-/
def IsDEssentialComponent (B : Set ℕ) : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → ∀ α ∈ Set.Ioo (0 : ℝ) 1, A.HasDensity α →
    α < (A + B).lowerDensity

set_option linter.style.formal_proof_palomar false in
/--
**Question 16.9.** Is every set $B \subseteq \mathbb{N}$ with $\overline{d}(B) = 1$ a
$d$-essential component?

As in the paper, `B` is a subset of $\{1, 2, 3, \ldots\}$, so it must avoid `0`.

The answer is no. Let $P_0 = 1$, $P_{s+1} = ((s+1) P_s)^4$ and
$B = \bigcup_{s \ge 0} (P_s, (s+1) P_s]$, so $\overline{d}(B) = 1$. Let
$A = \bigcup_{k \ge 1} [k^2, k^2 + k)$, so $d(A) = 1/2$. Below $M = P_{s+1}$ every element of
$B$ is at most $N = (s+1) P_s$, and $M = N^4$. An element of $A + B$ below $M$ that is not in $A$
lies within $N$ of the right end of one of the at most $N^2$ blocks of $A$ below $M$. So
$|(A + B) \cap [1, M)| \le |A \cap [1, M)| + N^3$, and $\underline{d}(A + B) \le 1/2 = d(A)$.
-/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/mnn31/erdos-lean/blob/997bfac3257131d4d82505b3d5d9b533e23c2d4a/ErdosLean/AcRiQuestion169.lean#L348-L353"]
theorem isDEssentialComponent_of_upperDensity_eq_one :
    ¬ ∀ B : Set ℕ, 0 ∉ B → B.upperDensity = 1 → IsDEssentialComponent B := by
  sorry

end Arxiv.«2604.12864»
