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
# Erdős Problem 986

*References:*
- [erdosproblems.com/986](https://www.erdosproblems.com/986)
- [ChGr98] Chung, F. and Graham, R., *Erdős on Graphs: His Legacy of Unsolved Problems*.
  A K Peters, Ltd. (1998).
- [Br26] Bradač, D., Off-diagonal Ramsey numbers. arXiv:2605.28793 (2026).
- [Sp77] Spencer, J., Asymptotic lower bounds for Ramsey functions. Discrete Math. (1977), 69-76.
- [MaVe23] Mattheus, S. and Verstraëte, J., The asymptotics of $r(4,t)$. Ann. of Math. (2024),
  919-941.
- [AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., A note on Ramsey numbers. J. Combin. Theory
  Ser. A 29 (1980), 354-360.
- [Ki95] Kim, J. H., The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$. Random
  Structures Algorithms 7 (1995), 173-207.
- [OAI26a] OpenAI, The Sharp Logarithmic Exponent of $r(5,t)$. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026/paper.pdf
- [OAI26b] OpenAI, Sharp Logarithmic Exponents for Fixed Off-Diagonal Ramsey Numbers. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf
- [Ch26] Chen, K., A note on the logarithmic exponent of Ramsey number $r(4,t)$. arXiv:2610.15293
  (2026).
-/

@[expose] public section

open Filter

namespace Erdos986

set_option linter.style.formal_proof_palomar false in
/--
For any fixed $s\geq 3$,
$$R(s,k) \gg \frac{k^{s-1}}{(\log k)^c}$$
for some constant $c=c(s)>0$.

According to Chung and Graham [ChGr98] this was first conjectured by Erdős in 1947.

Proved by Bradač [Br26], with $c=2s-4$.

The linked formal proof (Codex and GPT-5.6 Sol) gives `k ^ (s - 1) / (log k) ^ c = O(R(s, k))`
for a natural `c > 0`, with the Ramsey number defined through `CliqueFree`/`IndepSetFree`; this
implies the statement below.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos986.lean#L92"]
theorem erdos_986 :
    ∀ (s : ℕ) (hs : 3 ≤ s),
      ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
        ∀ᶠ (k : ℕ) in atTop,
          (SimpleGraph.classicalRamsey s k : ℝ) ≥
            C * (k : ℝ) ^ (s - 1) / (Real.log k) ^ c := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For $s = 5$ the exponent of $\log k$ is sharp: for every $\varepsilon > 0$,
$$R(5,k) \geq \frac{k^4}{(\log k)^{3+\varepsilon}}$$
for all sufficiently large $k$. This matches the upper bound $R(5,k) \ll k^4/(\log k)^3$ of
Ajtai, Komlós and Szemerédi [AKS80] up to the $\varepsilon$.

Proved by an internal OpenAI model in September 2026 [OAI26a]; the linked Lean proof also gives
the upper bound.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Main.lean#L27"]
theorem erdos_986.variants.log_exponent_five :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
      (k : ℝ) ^ 4 / (Real.log k) ^ (3 + ε) ≤ SimpleGraph.classicalRamsey 5 k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For every fixed $s \geq 6$ the exponent of $\log k$ is sharp: for every $\varepsilon > 0$,
$$R(s,k) \geq \frac{k^{s-1}}{(\log k)^{s-2+\varepsilon}}$$
for all sufficiently large $k$. This matches the upper bound
$R(s,k) \ll k^{s-1}/(\log k)^{s-2}$ of Ajtai, Komlós and Szemerédi [AKS80] up to the
$\varepsilon$.

Proved by an internal OpenAI model in September 2026 [OAI26b]; the linked Lean proof also gives
the upper bound. For $s = 3$ the order of magnitude $R(3,k) \asymp k^2/\log k$ is due to Kim
[Ki95]. For $s = 4$, Mattheus and Verstraëte determined $R(4,k)$ up to a factor of order
$\log^2 k$ [MaVe23]; Chen [Ch26] observes that the bounds for $s \geq 5$, together with the
proof of the Ajtai–Erdős–Komlós–Szemerédi conjecture, give $R(4,k) = k^3/(\log k)^{2+o(1)}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/Main.lean#L12"]
theorem erdos_986.variants.log_exponent_ge_six :
    ∀ s : ℕ, 6 ≤ s → ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
      (k : ℝ) ^ (s - 1) / (Real.log k) ^ ((s : ℝ) - 2 + ε) ≤ SimpleGraph.classicalRamsey s k := by
  sorry

/-- `erdos_986.variants.log_exponent_five` gives the case $s = 5$ of `erdos_986`, with $c = 4$. -/
@[category test, AMS 5]
theorem erdos_986.variants.five_of_log_exponent_five
    (h : type_of% erdos_986.variants.log_exponent_five) :
    ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ ∀ᶠ (k : ℕ) in atTop,
      (SimpleGraph.classicalRamsey 5 k : ℝ) ≥ C * (k : ℝ) ^ (5 - 1) / (Real.log k) ^ c := by
  refine ⟨4, 1, by norm_num, by norm_num, ?_⟩
  filter_upwards [h 1 one_pos] with k hk
  have h4 : (3 : ℝ) + 1 = 4 := by norm_num
  rw [h4] at hk
  simpa using hk

end Erdos986
