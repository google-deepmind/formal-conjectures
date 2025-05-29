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
# Erdős Problem 897

*Reference:* [erdosproblems.com/897](https://www.erdosproblems.com/897)
-/
--TODO(lezeau): add `ArithmeticFunction.IsAdditive` to `ForMathlib`

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$ such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$.
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?
-/
@[category research open, AMS 11]
theorem erdos_897.parts.i
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hf' : (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) :
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$.
Is it true that $\limsup_n f(n+1)/ f(n) = ∞$?
-/
@[category research open, AMS 11]
theorem erdos_897.parts.ii
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hf' : (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) :
    Filter.atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤ := by
  sorry

/--
Wirsing [Wi70] proved that if $|f(n+1)−f(n)| ≤ C$ then $f(n) = c \log n + O(1)$ for some constant
$c$.

[Wi70] Wirsing, E., _A characterization of $\log n$ as an additive arthemetic function_.
Symposia Math. (1970), 45-47.
-/
@[category research solved, AMS 11]
theorem erdos_897.variants.log_growth
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (C : ℝ) (hf' : ∀ n, |f (n+1) - f n| ≤ C) :
    ∃ c O, ∀ n, |f n - c*Real.log n| ≤ O := by
  sorry


/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$ and $f(p^k) = f(p)$
or $f(p^k) = kf(p)$.
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?
-/
@[category research open, AMS 11]
theorem erdos_897.variants.parts.i
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hf' : (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤)
    (hf'' : (∀ k p, p.Prime → f (p^k) = f p) ∨ (∀ (k p : ℕ), p.Prime → f (p^k) = k*f p)) :
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$ and $f(p^k) = f(p)$
or $f(p^k) = kf(p)$.
Is it true that $\limsup_n f(n+1)/f(n) = ∞$?
-/
@[category research open, AMS 11]
theorem erdos_897.variants.parts.ii
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hf' : (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤)
    (hf'' : (∀ k p, p.Prime → f (p^k) = f p) ∨ (∀ (k p : ℕ), p.Prime → f (p^k) = k*f p)) :
    Filter.atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤ := by
  sorry
