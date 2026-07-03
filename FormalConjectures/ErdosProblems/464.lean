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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 464

*References:*
- [erdosproblems.com/464](https://www.erdosproblems.com/464)
- [AkMo04] Akhunzhanov, R. K. and Moshchevitin, N. G., *On the chromatic number of a distance
  graph associated with a lacunary sequence*. Dokl. Akad. Nauk (2004), 295-296.
- [Du06] Dubickas, Artūras, *On the fractional parts of lacunary sequences*. Math. Scand. (2006),
  136-146.
- [Ka01] Katznelson, Y., *Chromatic numbers of Cayley graphs on $\mathbb{Z}$ and recurrence*.
  Combinatorica (2001), 211-219.
- [PeSc10] Peres, Yuval and Schlag, Wilhelm, *Two Erdős problems on lacunary sequences: chromatic
  number and Diophantine approximation*. Bull. Lond. Math. Soc. (2010), 295-300.
- [Po79b] Pollington, A. D., *On the density of sequence $\{n_k\xi\}$*. Illinois J. Math. (1979),
  511-515.
- [dM80] de Mathan, B., *Numbers contravening a condition in density modulo $1$*. Acta Math.
  Acad. Sci. Hungar. (1980), 237-241 (1981).
-/

namespace Erdos464

/- Formalization notes:
- Since every $\|\theta n_k\|$ lies in $[0,1/2]$, the literal reading of "$\{\|\theta n_k\|\}$
  is not dense in $[0,1]$" would be vacuously true. The intended (and solved) content is that
  the sequence $(\theta n_k)$ is not dense modulo one, which is how the conclusion is rendered
  here: `¬ Dense (Set.range fun k => (↑(θ * n k) : AddCircle (1 : ℝ)))`. This matches
  `pollington_de_mathan` in `Problem10_6.lean` of the Bugeaud collection, which formalizes the
  full-Hausdorff-dimension version of the same de Mathan–Pollington theorem. It is implied by
  the $\inf_{k\geq 1}\|\theta n_k\| > 0$ that de Mathan and Pollington prove.
- The lacunarity hypothesis is rendered by the house predicate `IsLacunary`
  ($\exists c > 1$ with $c \cdot n_k < n_{k+1}$ for all sufficiently large $k$), as in
  `erdos_355`; for a strictly increasing sequence of positive integers the problem's condition
  $n_{k+1} \geq (1+\epsilon) n_k$ for all $k$ implies `IsLacunary`, and modifying finitely many
  terms does not affect density modulo one.
-/

/--
Let $A=\{n_1<n_2<\cdots\}\subset \mathbb{N}$ be a lacunary sequence (so there exists some
$\epsilon>0$ with $n_{k+1}\geq (1+\epsilon)n_k$ for all $k$). Must there exist an irrational
$\theta$ such that
$$\{ \|\theta n_k\| : k\geq 1\}$$
is not dense in $[0,1]$ (where $\| x\|$ is the distance to the nearest integer)?

Solved independently by de Mathan [dM80] and Pollington [Po79b], who showed that, given any
such $A$, there exists such a $\theta$, with
$$\inf_{k\geq 1}\| \theta n_k\| \gg \frac{\epsilon^4}{\log(1/\epsilon)}.$$
This bound was improved by Katznelson [Ka01], Akhunzhanov and Moshchevitin [AkMo04], and
Dubickas [Du06], before Peres and Schlag [PeSc10] improved it to
$$\inf_{k\geq 1}\| \theta n_k\| \gg \frac{\epsilon}{\log(1/\epsilon)},$$
and note that the best bound possible here would be $\gg \epsilon$.

This problem has consequences for [894](https://www.erdosproblems.com/894).

The conclusion "$\{\|\theta n_k\|\}$ is not dense in $[0,1]$" is formalized as the sequence
$(\theta n_k)$ not being dense modulo one; see the formalization notes above.
-/
@[category research solved, AMS 11]
theorem erdos_464 : answer(True) ↔
    ∀ n : ℕ → ℕ, StrictMono n → (∀ k, 0 < n k) → IsLacunary n →
      ∃ θ : ℝ, Irrational θ ∧
        ¬ Dense (Set.range fun k => (↑(θ * n k) : AddCircle (1 : ℝ))) := by
  sorry

end Erdos464
