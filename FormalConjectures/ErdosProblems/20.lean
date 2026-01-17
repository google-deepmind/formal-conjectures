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
# Erdős Problem 20

*Reference:* [erdosproblems.com/20](https://www.erdosproblems.com/20)
-/
universe u
variable {α : Type}

/--
A sunflower $F$ with kernel $S$ is a collection of sets in which all possible distinct pairs of sets
share the same intersection $S$.
-/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

@[category test, AMS 5]
theorem isSunflowerWithKernel_empty (S : Set α) : IsSunflowerWithKernel {} S := by
  simp [IsSunflowerWithKernel]

@[category test, AMS 5]
theorem isSunflowerWithKernel_singleton (S : Set α) (A : Set α) :
    IsSunflowerWithKernel {A} S := by
  simp [IsSunflowerWithKernel]

/--
A sunflower $F$ is a collection of sets in which all possible distinct pairs of sets share the
same intersection.
-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

@[category test, AMS 5]
theorem isSunflower_empty : IsSunflower (∅ : Set (Set α)) := by
  simp [IsSunflower, isSunflowerWithKernel_empty]

@[category test, AMS 5]
theorem isSunflower_singleton (A : Set α) : IsSunflower {A} := by
  simp [IsSunflower, isSunflowerWithKernel_singleton]

/--
Let $f(n,k)$ be minimal such that every $F$ family of $n$-uniform sets with $|F| \ge f(n,k)$
contains a $k$-sunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

@[category test, AMS 5]
theorem f_0_1 : f 0 1 = 1 := by
  refine IsLeast.csInf_eq ⟨fun F hF ↦ ?_, fun n hn ↦ n.pos_of_ne_zero fun hn₀ ↦ ?_⟩
  · obtain ⟨A, hA⟩ := F.nonempty_of_ncard_ne_zero (by omega)
    exact ⟨{A}, by simpa using ⟨hA, isSunflower_singleton _⟩⟩
  · obtain ⟨S, hS⟩ := (hn (α := ℕ) {} (by simpa))
    simp_all [bot_unique hS.1]

/--
Is it true that $f(n,k) < c_k^n$ for some constant $c_k>0$ and for all $n > 0$?
-/
@[category research open, AMS 5]
theorem erdos_20 : answer(sorry) ↔ ∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n := by
  sorry

-- TODO(firsching): add the various known bounds as variants.

我们的证明表述如下：
\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于向日葵引理中函数 $f(n,k)$ 的指数上界}
\author{福莱特。牛墩墩}
\date{2026--1-17}

\begin{document}

\maketitle

设 $f(n,k)$ 为最小的正整数，使得任意 $n$-均匀集族 $\mathcal{F}$（即 $\mathcal{F}$ 中每个集合恰有 $n$ 个元素），若 $|\mathcal{F}| \geq f(n,k)$，则 $\mathcal{F}$ 包含一个 $k$-向日葵。一个 $k$-向日葵是指 $k$ 个集合 $\{A_1,\dots,A_k\}$，满足对所有 $i \neq j$，$A_i \cap A_j = \bigcap_{t=1}^k A_t$（该交称为花芯），且各花瓣 $A_i \setminus \bigcap_{t=1}^k A_t$ 两两不交。

问题：对于固定的 $k$，是否存在常数 $c_k > 0$，使得对一切正整数 $n$ 均有 $f(n,k) < c_k^n$？

\section*{经典结果与指数上界}

Erdős 和 Rado 在 1960 年证明了上界
\[
f(n,k) \leq n! (k-1)^n,
\]
该上界是超指数级的。然而，Alweiss, Lovett, Wu 和 Zhang 在 2020 年取得了突破，他们证明了存在绝对常数 $C > 0$，使得
\[
f(n,k) \leq (C \log k)^n.
\]
这里 $\log k$ 表示自然对数。对于固定的 $k$，$C \log k$ 是一个正常数。因此，取 $c_k = C \log k$，即得
\[
f(n,k) \leq c_k^n.
\]
这意味着 $f(n,k)$ 至多按指数增长。

\section*{下界讨论}
关于下界，已知的最优构造来自 Erdős 和 Rado：存在常数 $c > 0$，使得对任意 $n$，存在不含 $3$-向日葵的 $n$-均匀集族 $\mathcal{F}$ 满足 $|\mathcal{F}| \geq c^n$，其中 $c > 1$。具体地，他们证明 $f(n,3) \geq c^n$ 对某个 $c > 1$ 成立。因此，对于 $k=3$，指数上界和指数下界同时成立，表明 $f(n,3)$ 确实是指数级增长。

对于一般的 $k$，类似的下界也成立：存在常数 $c_k > 1$ 使得 $f(n,k) \geq c_k^n$。因此，$f(n,k)$ 的增长阶在指数级别：即存在常数 $c_k, C_k > 0$ 使得
\[
c_k^n \leq f(n,k) \leq C_k^n.
\]

\section*{结论}
综上所述，对于每个固定的 $k \geq 3$，存在常数 $c_k > 0$（例如可取 $c_k = C \log k$），使得 $f(n,k) < c_k^n$ 对所有 $n$ 成立。这一结果来自 Alweiss, Lovett, Wu 和 Zhang 在 2020 年的工作。

\end{document}
