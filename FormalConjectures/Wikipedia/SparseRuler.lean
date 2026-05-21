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

import FormalConjectures.ErdosProblems.«170»

/-!
# Sparse Ruler

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Sparse_ruler)

A sparse ruler of length $L$ is a sequence of marks $0 = a_1 < a_2 < \dots < a_m = L$.
A distance $k \in \mathbb{N}$ can be measured if there are $i, j \in \{1, \dots, m\}$, such that
$k = a_j - a_i$.

One can now ask for rulers that measure every integer up to some $K \in \mathbb{N}$ and for them
to be minimal, i.e. having a minimal number of marks. Furthermore, we can restrict such rulers in
length, for example requiring for a ruler of length $L$ to measure every distance up to $L$. This
is called a perfect ruler and Erdős Problem 170 covers the question of how many marks such minimum
perfect rulers have asymptotically.

There are several other questions with regards to sparse rulers and many of them are still unsolved.
-/

namespace SparseRuler

/- TODO: add statements from Wikipedia -/

end SparseRuler
