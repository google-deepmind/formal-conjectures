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
# Identification of sampled and aggregated autoregressions

*Reference:* Marko Mlikota,
[Parameter Identification and Inference in Discretely Sampled or Temporally Aggregated
Autoregressions](https://arxiv.org/abs/2608.13224v2), version 2, headed 10 September 2026.
Conjectures 1 and 2 appear on [printed page 2](https://arxiv.org/pdf/2608.13224v2#page=3).
Section 3 defines the competing parameter space and observational equivalence on
[printed page 10](https://arxiv.org/pdf/2608.13224v2#page=11).

The true process is an integer-time centered stationary Gaussian autoregression of exact order
$p$. Its dynamic roots are nonzero, have modulus less than one, and have distinct $q$th powers.
Competitors range over every stationary autoregression of order at most $p$, with any positive
innovation variance. Observational equivalence is equality of the full observed path laws.
-/

@[expose] public section

namespace Arxiv.«2608.13224»

open MeasureTheory TimeSeries.Autoregression

/--
Mlikota's Conjecture 1: stock observations $y_t=x_{qt}$ identify the coefficient vector and
innovation variance when $q$ is odd. For even $q$, the identified set consists of the true
parameter and its alternating-sign coefficient transform, with unchanged innovation variance.

The restrictions on exact order and powered dynamic roots apply only to the true parameter.
The case $q=1$ is Proposition 3. Proposition 5(ii) proves membership of the sign transform for
even $q$; Proposition 5(iii)–(iv) proves the conjecture for $q=2$ and for real dynamic roots.
-/
@[category research open, AMS 60 62]
theorem stock_identified_set {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (θ : Parameter p) (hstationary : θ.IsStationary) (hexact : θ.HasExactOrder)
    (hroots : θ.HasDistinctPoweredRoots q) (μ : Measure Path) (hμ : IsGaussianARLaw θ μ) :
    stockIdentifiedSet p q μ = if Even q then {θ, θ.signFlip} else {θ} := by
  sorry

/--
Mlikota's Conjecture 2: nonoverlapping flow observations
$y_t=\sum_{s=0}^{q-1}x_{qt-s}$ identify both the coefficient vector and innovation variance
for every positive $q$.

The case $q=1$ is Proposition 3. Proposition 7(ii) proves the case $q=2$, and Proposition 7(iv)
proves the case of real dynamic roots with odd $q$. Proposition 7(iii) excludes the alternating
sign transform when $q$ is even.
-/
@[category research open, AMS 60 62]
theorem flow_identified_set {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (θ : Parameter p) (hstationary : θ.IsStationary) (hexact : θ.HasExactOrder)
    (hroots : θ.HasDistinctPoweredRoots q) (μ : Measure Path) (hμ : IsGaussianARLaw θ μ) :
    flowIdentifiedSet p q μ = {θ} := by
  sorry

end Arxiv.«2608.13224»
