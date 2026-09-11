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

import FormalConjecturesUtil

/-!
# Erdős Problem 897

*References:*
- [erdosproblems.com/897](https://www.erdosproblems.com/897)
- [Ar25] Archivara Math Research Agent, [An Additive Counterexample: Erdős Problem 897](https://archivara.org/paper/df04f023-6ef0-4c52-bd12-18cdaa8f0741) (2025)
- [ArWu25] Aristotle, operated mostly by L. Wu, [Lean formalisation of Erdős problem 897](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) (2025)
- [Wi70] E. Wirsing, A characterization of $\log n$ as an additive arithmetic function.
  Symposia Math. (1970), 45-57.
- [Wi81] E. Wirsing, Additive and completely additive functions with restricted growth.
  Recent progress in analytic number theory, Vol. 2 (Durham, 1979), 231--280 (1981).
-/

open Filter ArithmeticFunction

namespace Erdos897

/--
The growth hypothesis $\limsup_{p,k} f(p^k)/\log(p^k) = \infty$ of [erdosproblems.com/897]:
the normalised values $f(q)/\log q$ of $f$ are unbounded above as $q$ ranges over prime powers.

The $\limsup$ is taken along prime powers $q = p^k \to \infty$, which allows a fixed prime with
unbounded exponent (e.g. $q = 2^k$, as in [Ar25, Lemma 1]). It is *not* the joint limit
$p, k \to \infty$, which would be a strictly stronger assumption.
-/
def LimsupPrimePowEqTop (f : ArithmeticFunction ℝ) : Prop :=
  (atTop ⊓ 𝓟 {q : ℕ | IsPrimePow q}).limsup (fun q => (f q / Real.log q : EReal)) = ⊤

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$.
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?

The answer is no; this follows from a construction of Wirsing [Wi81], rediscovered by
Archivara [Ar25] and formalised in Lean by Aristotle [ArWu25]. The linked formalisation
proves an earlier phrasing of this statement (with the growth hypothesis taken along
$p, k \to \infty$ jointly); its counterexample satisfies the hypothesis as stated here as well,
since $f(q)/\log q = \log^*(q)$ for every prime power $q$ [ArWu25, Lemma 1].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean"]
theorem erdos_897.parts.i : answer(False) ↔ ∀ (f : ArithmeticFunction ℝ),
    f.IsAdditive → LimsupPrimePowEqTop f →
    atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$.
Is it true that $\limsup_n f(n+1)/ f(n) = ∞$?

The answer is no; the same counterexample is formalised in Lean by Aristotle [ArWu25]
(see the remark in `erdos_897.parts.i` about the phrasing of the growth hypothesis).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean"]
theorem erdos_897.parts.ii : answer(False) ↔ ∀ (f : ArithmeticFunction ℝ),
    f.IsAdditive → LimsupPrimePowEqTop f →
    atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤ := by
  sorry

/--
Wirsing [Wi70] proved that if $|f(n+1)−f(n)| ≤ C$ then $f(n) = c \log n + O(1)$ for some constant
$c$.
-/
@[category research solved, AMS 11]
theorem erdos_897.variants.log_growth
    (f : ArithmeticFunction ℝ) (hf : f.IsAdditive)
    (C : ℝ) (hf' : ∀ n, |f (n+1) - f n| ≤ C) :
    ∃ c, ∃ (O : ℕ → ℝ), O =O[atTop] (1 : ℕ → ℝ) ∧
      ∀ n, f n = c*Real.log n + O n := by
  sorry

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$.
Assume moreover that $f(p^k) = f(p)$ for all primes $p$ and $k \geq 1$ (i.e. $f$ is strongly
additive), or that $f(p^k) = kf(p)$ for all primes $p$ and $k$ (i.e. $f$ is completely additive).
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?

The known counterexample does not satisfy either of these extra hypotheses, so this variant remains
open.
-/
@[category research open, AMS 11]
theorem erdos_897.variants.parts.i : answer(sorry) ↔ ∀ (f : ArithmeticFunction ℝ),
    f.IsAdditive → LimsupPrimePowEqTop f →
    (f.IsStronglyAdditive ∨ f.IsCompletelyAdditive) →
    atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$.
Assume moreover that $f(p^k) = f(p)$ for all primes $p$ and $k \geq 1$ (i.e. $f$ is strongly
additive), or that $f(p^k) = kf(p)$ for all primes $p$ and $k$ (i.e. $f$ is completely additive).
Is it true that $\limsup_n f(n+1)/f(n) = ∞$?

The known counterexample does not satisfy either of these extra hypotheses, so this variant remains
open.
-/
@[category research open, AMS 11]
theorem erdos_897.variants.parts.ii : answer(sorry) ↔ ∀ (f : ArithmeticFunction ℝ),
    f.IsAdditive → LimsupPrimePowEqTop f →
    (f.IsStronglyAdditive ∨ f.IsCompletelyAdditive) →
    atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤ := by
  sorry

end Erdos897
