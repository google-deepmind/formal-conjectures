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
import FormalConjectures.Wikipedia.CollatzConjecture

/-!
# Erdős Problem 1135

*Reference:*
* [erdosproblems.com/1135](__https://www.erdosproblems.com/1135__)
* [Gu04] Guy, Richard K., Unsolved problems in number theory.  (2004), xviii+437.
* [La10] Lagarias, Jeffrey C., The {$3x+1$} problem: an overview.  (2010), 3--29.
* [La16] Lagarias, Jeffrey C., Erd\H os, {K}larner, and the {$3x+1$} problem. Amer. Math. Monthly (2016), 753--776.
* [La85] Lagarias, Jeffrey C., The {$3x+1$} problem and its generalizations. Amer. Math. Monthly (1985), 3--23.
-/

namespace Erdos1135

/-!The **Collatz conjecture** states that for any positive integer $n$, there exists a natural number $m$ such that the $m$-th term of the sequence is 1.
-/
@[category research open, AMS 11 37]
alias erdos_1135 := CollatzConjecture.collatzConjecture

end Erdos1135
