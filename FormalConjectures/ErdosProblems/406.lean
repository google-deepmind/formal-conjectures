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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 406

*References:*
- [erdosproblems.com/406](https://www.erdosproblems.com/406)
- Erdős, P., *Some unconventional problems in number theory*, Mathematics Magazine **52** (1979),
  67–70. The ternary-digit question also appears as problem B33 in Guy, R. K.,
  *Unsolved Problems in Number Theory*.
- Lagarias, J. C., *Ternary expansions of powers of 2*, J. London Math. Soc. **79** (2009),
  562–588.
- Saye, R. I., *On two conjectures concerning the ternary digits of powers of two*,
  J. Integer Seq. **25** (2022), Article 22.3.4. [arXiv:2202.13256](https://arxiv.org/abs/2202.13256)
- Idowu, M. A., *Repunit Coordinates for the Erdős Ternary-Digit Problem*,
  [arXiv:2610.03789](https://arxiv.org/abs/2610.03789)
- OEIS [A351927](https://oeis.org/A351927), [A351928](https://oeis.org/A351928)

The conjecture has three equivalent forms, all recorded below: the finiteness form
(`erdos_406`), the exact classification (`erdos_406.strong`), and the per-exponent form
(`Arxiv.«2107.12475».CollatzLike`). Saye verified the per-exponent form for
$n \le 2 \cdot 3^{45} \approx 5.9 \times 10^{21}$; the finiteness question remains open.
-/

@[expose] public section

namespace Erdos406

/--
Is it true that there are only finitely many powers of $2$ which have only the digits $0$
and $1$ when written in base $3$?
-/
@[category research open, question, AMS 11]
theorem erdos_406 : { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  sorry

/--
**Strong form.** The only powers of $2$ whose base-$3$ expansion uses only the digits $0$ and
$1$ are $2^0 = 1$, $2^2 = 4$ and $2^8 = 256$. Equivalently, $2^n$ has no digit $2$ in base
$3$ exactly when $n \in \{0, 2, 8\}$.

This is the form conjectured by Erdős, and it implies the finiteness statement `erdos_406`.
The per-exponent form is `Arxiv.«2107.12475».CollatzLike`.
-/
@[category research open, AMS 11]
theorem erdos_406.strong :
    { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] } = {1, 4, 256} := by
  sorry

/--
If we only allow the digits $1$ and $2$ then $2^{15}$ seems to be the largest such power
of $2$.
-/
@[category research open, AMS 11]
theorem erdos_406.variants.one_two :
    IsGreatest { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } (2 ^ 15) := by
  sorry

end Erdos406
