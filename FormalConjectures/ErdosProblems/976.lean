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

import FormalConjecturesUtil

/-!
# Erdős Problem 976

*References:*
- [erdosproblems.com/976](https://www.erdosproblems.com/976)
- [Er52c] Erdős, P., On the greatest prime factor of $\prod_{k=1}^{x} f(k)$. J. London Math. Soc.
  (1952), 379--384.
- [Er65b] Erdős, Paul, Some recent advances and current problems in number theory. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [ErSc90] Erdős, P. and Schinzel, A., On the greatest prime factor of $\prod_{k=1}^{x} f(k)$.
  Acta Arith. (1990), 191--200.
- [Na22] Nagell, Abhandlungen aus dem Math. Seminar Hamburg (1922), 179-194.
- [Ri34] Ricci, G., Annali de Mat. (1934), 295-303.
- [Te90] Tenenbaum, Gérald, Sur une question d'Erdős et Schinzel. (1990), 405--443.
-/

open Filter Real Polynomial

open scoped Asymptotics

namespace Erdos976

/--
$F_f(n)$ is the largest prime dividing $f(m)$ for some $1 \le m \le n$. Equivalently, it is the
greatest prime divisor of $\prod_{1 \le m \le n} f(m)$ whenever this product is nonzero.
-/
noncomputable def F (f : ℤ[X]) (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup fun m ↦ (f.eval (m : ℤ)).natAbs.maxPrimeFac

/-- $F_f(0) = 0$. -/
@[category test, AMS 11]
theorem F_zero (f : ℤ[X]) : F f 0 = 0 := by
  simp [F]

/-- $F_{X^2+1}(1) = 2$. -/
@[category test, AMS 11]
theorem F_X_sq_add_one_one : F (X ^ 2 + 1) 1 = 2 := by
  simp [F, Finset.Icc_self]
  native_decide

/--
Let $f\in \mathbb{Z}[x]$ be an irreducible polynomial of degree $d\geq 2$. Let $F_f(n)$ be maximal
such that there exists $1\leq m\leq n$ with $f(m)$ divisible by a prime $\geq F_f(n)$.
Equivalently, $F_f(n)$ is the greatest prime divisor of
$$
\prod_{1\leq m\leq n} f(m).
$$
Estimate $F_f(n)$. In particular, is it true that $F_f(n)\gg n^{1+c}$ for some constant $c>0$?
-/
@[category research open, AMS 11]
theorem erdos_976 : answer(sorry) ↔
    ∀ (f : ℤ[X]), Irreducible f → 2 ≤ f.natDegree →
      ∃ c > (0 : ℝ), (fun n : ℕ ↦ (n : ℝ) ^ (1 + c)) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Is it even true that $F_f(n)\gg n^d$?
-/
@[category research open, AMS 11]
theorem erdos_976.variants.degree : answer(sorry) ↔
    ∀ (f : ℤ[X]), Irreducible f → 2 ≤ f.natDegree →
      (fun n : ℕ ↦ (n : ℝ) ^ f.natDegree) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Nagell [Na22] and Ricci [Ri34] proved that $F_f(n)\gg n\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.nagell_ricci {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    (fun n : ℕ ↦ (n : ℝ) * log n) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

/--
Erdős [Er52c] improved the bound to $F_f(n)\gg n(\log n)^{\log\log\log n}$.
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.erdos {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    (fun n : ℕ ↦ (n : ℝ) * log n ^ log (log (log n))) =O[atTop]
      fun n ↦ (F f n : ℝ) := by
  sorry

/--
Tenenbaum [Te90] proved that $F_f(n)\gg n\exp((\log n)^c)$ for some constant $c>0$.
Erdős [Er65b] had claimed this bound but never published a proof, and the argument appears to
have been flawed; Erdős and Schinzel [ErSc90] later published a weaker bound.
-/
@[category research solved, AMS 11]
theorem erdos_976.variants.tenenbaum {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ c > (0 : ℝ),
      (fun n : ℕ ↦ (n : ℝ) * exp (log n ^ c)) =O[atTop] fun n ↦ (F f n : ℝ) := by
  sorry

end Erdos976
