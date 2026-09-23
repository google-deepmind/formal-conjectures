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
# Falconer's distance set conjecture

If $d \ge 2$ and $E \subseteq \mathbb{R}^d$ is compact with $\dim_H E > \frac{d}{2}$, then the
distance set
$$\{ |x - y| \mid x, y \in E \}$$
has positive Lebesgue measure. The restriction $d \ge 2$ is needed; see `falconer_conjecture`.

## References

* [K. Falconer, *On the Hausdorff dimensions of distance sets*](https://doi.org/10.1112/S0025579300010998)
* [Wikipedia, *Falconer's conjecture*](https://en.wikipedia.org/wiki/Falconer%27s_conjecture)
-/

open MeasureTheory Set

open scoped ENNReal EuclideanGeometry

/-- Falconer's distance set conjecture, $d = 2$ case. -/
@[category research open, AMS 28 42]
lemma falconer_conjecture_two (E : Set <| ℝ²) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    0 < volume (image2 dist E E) := sorry

/-- Falconer's distance set conjecture in dimension $d \ge 2$.

The hypothesis $2 \le d$ excludes a degenerate case: the conclusion is false for $d = 1$.
The base-$7$ Cantor set $E = \{\sum_{n \ge 1} a_n 7^{-n} : a_n \in \{0, 1, 2\}\}$ is compact
with $\dim_H E = \log 3 / \log 7 > 1/2$, but $E - E$ has digits in $\{-2, \dots, 2\}$, so
after fixing $n$ digits it is covered by $5^n$ intervals of length $\frac{2}{3} 7^{-n}$ and is
therefore null; its distance set is the image of $E - E$ under $|\cdot|$ and is null too. -/
@[category research open, AMS 28 42]
lemma falconer_conjecture (d : ℕ) (h2d : 2 ≤ d) (E : Set <| ℝ^d) (hc : IsCompact E)
    (hd : d < 2 * dimH E) :
    0 < volume (image2 dist E E) := sorry
