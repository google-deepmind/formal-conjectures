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
# Erdős Problem 976

*References:*
- [erdosproblems.com/976](https://www.erdosproblems.com/976)
- [Er52c] Erdős, P., *On the greatest prime factor of $\prod_{k=1}^x f(k)$*. J. London Math. Soc.
  27 (1952), 379-384.
- [Er65b] Erdős, P., *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Na22] Nagell, T., Abh. Math. Sem. Hamburg 1 (1922), 179-194.
- [Ri34] Ricci, G., Annali di Mat. (1934), 295-303.
- [Te90] Tenenbaum, G., *Sur une question d'Erdős et Schinzel*. A tribute to Paul Erdős (1990),
  405-443.
-/

@[expose] public section

open Filter Asymptotics Polynomial

namespace Erdos976

/-- $F_f(n)$, the greatest prime divisor of $\prod_{1\leq m\leq n} f(m)$. If $f$ has no integer
root the product is nonzero; `Nat.maxPrimeFac` of $0$ or $1$ is a junk value that does not
matter for large $n$. -/
noncomputable def F (f : ℤ[X]) (n : ℕ) : ℕ :=
  (∏ m ∈ Finset.Icc 1 n, f.eval (m : ℤ)).natAbs.maxPrimeFac

def erdos_976.answer : ℤ[X] → ℕ → ℝ := sorry

/--
Let $f\in \mathbb{Z}[x]$ be an irreducible polynomial of degree $d\geq 2$. Let $F_f(n)$ be maximal
such that there exists $1\leq m\leq n$ with $f(m)$ is divisible by a prime $\geq F_f(n)$.
Equivalently, $F_f(n)$ is the greatest prime divisor of
$$\prod_{1\leq m\leq n}f(m).$$
Estimate $F_f(n)$.

We read "estimate" as determining the order of magnitude of $F_f(n)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_976 (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    (fun n ↦ (F f n : ℝ)) =Θ[atTop] erdos_976.answer f := by
  sorry

/--
Let $f\in \mathbb{Z}[x]$ be an irreducible polynomial of degree $d\geq 2$, and let $F_f(n)$ be the
greatest prime divisor of $\prod_{1\leq m\leq n}f(m)$. Is it true that $F_f(n)\gg n^{1+c}$ for some
constant $c>0$?
-/
@[category research open, question, AMS 11]
theorem erdos_976.parts.i :
    ∀ f : ℤ[X], Irreducible f → 2 ≤ f.natDegree →
      ∃ c > (0 : ℝ), (fun n : ℕ ↦ (n : ℝ) ^ (1 + c)) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Let $f\in \mathbb{Z}[x]$ be an irreducible polynomial of degree $d\geq 2$, and let $F_f(n)$ be the
greatest prime divisor of $\prod_{1\leq m\leq n}f(m)$. Is it true that $F_f(n)\gg n^d$?
-/
@[category research open, question, AMS 11]
theorem erdos_976.parts.ii :
    ∀ f : ℤ[X], Irreducible f → 2 ≤ f.natDegree →
      (fun n : ℕ ↦ (n : ℝ) ^ f.natDegree) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Nagell [Na22] and Ricci [Ri34] proved that $F_f(n) \gg n\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.nagell_ricci (f : ℤ[X]) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    (fun n : ℕ ↦ (n : ℝ) * Real.log n) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Erdős [Er52c] improved the bound of Nagell and Ricci to
$$F_f(n) \gg n(\log n)^{\log\log\log n}.$$
More precisely, [Er52c] gives $F_f(n) > n(\log n)^{c\log\log\log n}$ for some constant
$c = c(f) > 0$; the site omits $c$.
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.erdos (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ c > (0 : ℝ),
      (fun n : ℕ ↦ (n : ℝ) * Real.log n ^ (c * Real.log (Real.log (Real.log n)))) =O[atTop]
        fun n ↦ (F f n : ℝ) := by
  sorry

/--
In [Er65b] Erdős claimed a proof of $F_f(n) \gg n\exp((\log n)^c)$ for some constant $c>0$, but
never published it. A proof was provided by Tenenbaum [Te90].
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.tenenbaum (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ c > (0 : ℝ), (fun n : ℕ ↦ (n : ℝ) * Real.exp (Real.log n ^ c)) =O[atTop]
      fun n ↦ (F f n : ℝ) := by
  sorry

end Erdos976
