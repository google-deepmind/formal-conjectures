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
# Erdős Problem 981

*References:*
- [erdosproblems.com/981](https://www.erdosproblems.com/981)
- [El69] Elliott, P. D. T. A., *A conjecture of Erdős concerning character sums*.
  Indag. Math. 31 (1969), 164–171.
- [TaZh25] [arxiv/2512.24631](https://arxiv.org/abs/2512.24631)
  **Average first-passage times for character sums** by *Quanyu Tang and Hao Zhang*
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos981

/--
Property of a natural $N$ to satisfy $\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$,
where $\left(\frac{n}{p}\right)$ is the Jacobi symbol. The theorem statement mentions Legendre symbol,
however in formalization we use Jacobi symbol to avoid problem with passing the fact that $p$ is prime.
For prime $p$ `jacobiSym n p = legendreSym p n`.
-/
def Erdos981Property (ε : ℝ) (p : ℕ) (N : ℕ) : Prop :=
   (∑ n ≤ N, jacobiSym n p) < ε * N

/--
The smallest integer $m$ such that
$\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$ for all $N\geq m$.
-/
noncomputable def f (ε : ℝ) (p : ℕ) : ℕ :=
  sInf { m | ∀ N ≥ m, Erdos981Property ε p N }

/--
The smallest integer $m$ such that $\sum_{n\leq m} \left(\frac{n}{p}\right)<\epsilon m$
-/
noncomputable def f' (ε : ℝ) (p : ℕ) : ℕ :=
  sInf { m | Erdos981Property ε p m }

/--
Let $\epsilon > 0$ and $f_\epsilon(p)$ be the smallest integer $m$
such that $\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$ for all $N\geq m$. Prove that
$$\sum_{p<x}f_\epsilon(p)\sim c_\epsilon \frac{x}{\log x}$$
for some $c_\epsilon > 0$.

Proved by Elliott [El69].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos981.lean#L42"]
theorem erdos_981 (ε : ℝ) (hε : 0 < ε) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f ε p) * log x / x) atTop (𝓝 c) := by
  sorry

/--
Let $\epsilon > 0$ and $f_\epsilon(p)$ be the smallest integer $m$ such that $\sum_{n\leq m} \left(\frac{n}{p}\right)<\epsilon m$. Prove that
$$\sum_{p<x}f_\epsilon(p)\sim c_\epsilon \frac{x}{\log x}$$
for some $c_\epsilon > 0$.

Proved by Tang and Zhang [TaZh25].
-/
@[category research solved, AMS 11]
theorem erdos_981.variants.first_time (ε : ℝ) (hε : 0 < ε) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c) := by
  sorry

end Erdos981
