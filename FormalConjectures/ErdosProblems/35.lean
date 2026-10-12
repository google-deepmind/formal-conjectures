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
# Erdős Problem 35

*References:*
- [erdosproblems.com/35](https://www.erdosproblems.com/35)
- [Er56] Erdős, P., *Problems and results in additive number theory*. Colloque sur la Théorie des
  Nombres, Bruxelles, 1955 (1956), 127-137.
- [Er36c] Erdős, P., *On the arithmetical density of the sum of two sequences, one of which forms
  a basis for the integers*. Acta. Arith. (1936), 197-200.
- [Pl70] Plünnecke, H., *Eine zahlentheoretische Anwendung der Graphentheorie*. J. Reine. Angew.
  Math. (1970), 171-183.
-/

@[expose] public section

open Set Pointwise

namespace Erdos35

open scoped Classical in
/--
Let $B\subseteq\mathbb{N}$ be an additive basis of order $k$ with $0\in B$. Is it true that for
every $A\subseteq\mathbb{N}$ we have
$$d_s(A+B)\geq \alpha+\frac{\alpha(1-\alpha)}{k},$$
where $\alpha=d_s(A)$ and
$$d_s(A) = \inf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N}$$
is the Schnirelmann density?

Erdős [Er36c] proved this is true with $k$ replaced by $2k$ in the denominator (in a stronger form
that only considers $A\cup (A+b)$ for some $b\in B$, see [38](https://www.erdosproblems.com/38)).

Ruzsa has observed that this follows immediately from the stronger fact proved by Plünnecke
[Pl70] that (under the same assumptions, and for $\alpha>0$)
$$d_S(A+B)\geq \alpha^{1-1/k}.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos35.lean#L1738"]
theorem erdos_35 : answer(True) ↔ ∀ (B : Set ℕ) (k : ℕ), 0 ∈ B → B.IsAddBasisOfOrder k →
    ∀ A : Set ℕ, schnirelmannDensity A +
      schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤ schnirelmannDensity (A + B) := by
  sorry

open scoped Classical in
/--
Plünnecke [Pl70] proved that if $B\subseteq\mathbb{N}$ is an additive basis of order $k$ with
$0\in B$ then $d_S(A+B)\geq d_s(A)^{1-1/k}$ for every $A\subseteq\mathbb{N}$ with $d_s(A)>0$.
-/
@[category research solved, AMS 11]
theorem erdos_35.variants.plunnecke (B : Set ℕ) (k : ℕ) (h0 : 0 ∈ B) (hB : B.IsAddBasisOfOrder k)
    (A : Set ℕ) (hA : 0 < schnirelmannDensity A) :
    schnirelmannDensity A ^ (1 - (k : ℝ)⁻¹) ≤ schnirelmannDensity (A + B) := by
  sorry

end Erdos35
