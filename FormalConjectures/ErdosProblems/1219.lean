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
# Erdős Problem 1219

*References:*
- [erdosproblems.com/1219](https://www.erdosproblems.com/1219)
- [ErHa71] Erdős, Paul and Hajnal, András, Unsolved problems in set theory. Axiomatic Set
  Theory, Proc. Sympos. Pure Math. XIII Part I (1971), 17-48.
- [Ko25b] Komjáth, Péter, The Erdős–Hajnal problem list. Bull. Symb. Log. (2025), 418-461.
- [Sh75] Shelah, Saharon, Notes on partition calculus. Infinite and finite sets (Colloq.,
  Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10, North-Holland (1975), 1257-1276.
-/

@[expose] public section

open Cardinal Ordinal Combinatorics

namespace Erdos1219

universe u

/--
Let $(n_k)$ be an increasing sequence of integers such that $2^{\aleph_{n_k}}$ is strictly
increasing, and $2^{\aleph_{n_0}} > \aleph_\omega$. Is it true that
$$\sum_k 2^{\aleph_{n_k}} \to (\aleph_\omega)^2?$$

Here $\sum_k 2^{\aleph_{n_k}}$ is the cardinal sum, and the partition relation is the classical
one with two colours: every $2$-colouring of the pairs of a set of that cardinality has a
monochromatic set of cardinality $\aleph_\omega$.

A problem of Erdős, Hajnal, and Rado [ErHa71], proved by Shelah [Sh75].
-/
@[category research solved, AMS 3 5, formal_proof using lean4 at
  "https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Solution.lean#L22"]
theorem erdos_1219 : answer(True) ↔
    ∀ n : ℕ → ℕ, StrictMono n →
      StrictMono (fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) →
      ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0) →
      cardinalPartitionRel (sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) 2 2 (fun _ => ℵ_ ω) := by
  sorry

/--
Under the hypotheses of `erdos_1219`, the target $\aleph_\omega$ is smaller than the source
$\sum_k 2^{\aleph_{n_k}}$, so the partition relation is not ruled out by cardinality.
-/
@[category test, AMS 3]
theorem erdos_1219.test.aleph_omega_lt_sum (n : ℕ → ℕ)
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    ℵ_ ω < sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k) :=
  h0.trans_le (le_sum _ 0)

end Erdos1219
