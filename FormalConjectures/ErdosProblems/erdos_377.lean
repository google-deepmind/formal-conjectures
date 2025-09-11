/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/377
import FormalConjectures.Util.ProblemImports


open Filter

open scoped Topology

/--
Is there some absolute constant $C > 0$ such that
$$
  \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p} \leq C
$$
for all $n$?
-/
@[problem_status open]
theorem erdos_377 : ∃ C > (0 : ℝ),
    ∀ (n : ℕ),
      ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p) ≤ C :=
  sorry

/--
Erdos, Graham, Ruzsa, and Straus proved that if
$$
  f(n) = \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p}
$$
and
$$
  \gamma_0 = \sum_{k = 2}^{\infty} \frac{\log k}{2^k}
then
$$
  \lim_{x\to\infty} \frac{1}{x}\sum_{n\leq x} f(n) = \gamma_0
$$

[EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., _On the prime factors of $(\sp{2n}\sb{n})$_. Math. Comp. (1975), 83-92.
-/
@[problem_status solved]
theorem erdos_377.variants.limit.i (f : ℕ → ℝ)
    (hf : ∀ n,
      f n = ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p))
    (γ₀ : ℝ)
    (hγ₀ : γ₀ = ∑' (k : ℕ), (k + 2 : ℝ).log / 2 ^ (k + 2)) :
    Tendsto (fun (x : ℕ) => (1 : ℝ) / x * ∑ n ∈ Finset.Icc 1 x, f n)
      atTop (𝓝 γ₀) :=
  sorry

/--
Erdos, Graham, Ruzsa, and Straus proved that if
$$
  f(n) = \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p}
$$
and
$$
  \gamma_0 = \sum_{k = 2}^{\infty} \frac{\log k}{2^k}
then
$$
  \lim_{x\to\infty} \frac{1}{x}\sum_{n\leq x} f(n)^2 = \gamma_0^2
$$

[EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., _On the prime factors of $(\sp{2n}\sb{n})$_. Math. Comp. (1975), 83-92.
-/
@[problem_status solved]
theorem erdos_377.variants.limit.ii (f : ℕ → ℝ)
    (hf : ∀ n,
      f n = ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p))
    (γ₀ : ℝ)
    (hγ₀ : γ₀ = ∑' (k : ℕ), (k + 2 : ℝ).log / 2 ^ (k + 2)) :
    Tendsto (fun (x : ℕ) => (1 : ℝ) / x * ∑ n ∈ Finset.Icc 1 x, f n ^ 2)
      atTop (𝓝 (γ₀ ^ 2)) :=
  sorry

/--
Erdos, Graham, Ruzsa, and Straus proved that if
$$
  f(n) = \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p}
$$
and
$$
  \gamma_0 = \sum_{k = 2}^{\infty} \frac{\log k}{2^k}
$$
then for almost all integers $f(m) = \gamma_0 + o(1)$.

[EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., _On the prime factors of $(\sp{2n}\sb{n})$_. Math. Comp. (1975), 83-92.
-/
@[problem_status solved]
theorem erdos_377.variants.ae (f : ℕ → ℝ)
    (hf : ∀ n,
      f n = ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p))
    (γ₀ : ℝ)
    (hγ₀ : γ₀ = ∑' (k : ℕ), (k + 2 : ℝ).log / 2 ^ (k + 2)) :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
      ∀ᶠ n in cofinite, f n = γ₀ + o n :=
  sorry

/--
Erdos, Graham, Ruzsa, and Straus proved that if
$$
  f(n) = \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p}
$$
then there is some constant $c < 1$ such that for all large $n$
$$
  f(n) \leq c \log\log n.
$$

[EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., _On the prime factors of $(\sp{2n}\sb{n})$_. Math. Comp. (1975), 83-92.
-/
@[problem_status solved]
theorem erdos_377.variants.ub (f : ℕ → ℝ)
    (hf : ∀ n,
      f n = ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p)) :
    ∃ c < (1 : ℝ),
      ∀ᶠ n in atTop, f n ≤ c * (n : ℝ).log.log :=
  sorry
