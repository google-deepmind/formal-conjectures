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
# Erdős Problem 486: Logarithmic density for sets avoiding modular subsets

*References:*
* [erdosproblems.com/486](https://www.erdosproblems.com/486)
* [Wa26] Wang, S., *A proposed solution to Erdős Problem 486* (2026),
  https://github.com/ShouqiaoW/erdos/blob/main/486/paper.pdf
-/

namespace Erdos486

/--
Let $A \subseteq \mathbb{N}$, and for each $n \in A$ choose some
$X_n \subseteq \mathbb{Z}/n\mathbb{Z}$. Let
$B = \{m \in \mathbb{N} : m \not\in X_n \pmod{n} \text{ for all } n \in A \text{ with } m > n\}$.
Must $B$ have a logarithmic density?

The set $A$ is encoded by taking $X_n = \emptyset$ for $n \notin A$. Only positive moduli
$n$ are considered, since $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$ would allow $B$ to be an
arbitrary set.

The answer is no: Wang [Wa26] (with GPT-5.6) constructed a congruence system whose survivor set
$B$ has lower logarithmic density at most $177/200$ and upper logarithmic density at least
$49/50$. The first linked formal proof establishes this for the real-cutoff normalisation
$\frac{1}{\log x}\sum_{m < x, m \in B} \frac{1}{m}$ with the moduli restricted to $A$; the
second derives the statement below (`Set.HasLogDensity`, all moduli) from it.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos486.lean#L20",
  formal_proof using formal_conjectures at
  "https://github.com/Konamiu/formal-conjectures/blob/c69df0584ca9767090f5a68c8f09f1ff3c93ab80/FormalConjectures/ErdosProblems/486.lean#L39"]
theorem erdos_486 : answer(False) ↔
    ∀ X : (n : ℕ) → Set (ZMod n),
      ∃ d, {m : ℕ | ∀ n, 0 < n → n < m → (m : ZMod n) ∉ X n}.HasLogDensity d := by
  sorry

end Erdos486
