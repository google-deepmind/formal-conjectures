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
# Erdős Problem 518

*References:*
- [erdosproblems.com/518](https://www.erdosproblems.com/518)
- [ErGy95] Erdős, Paul and Gyárfás, András, _Vertex covering with monochromatic paths_.
  Math. Pannon. (1995), 7–10.
- [PVW24] Pokrovskiy, Alexey, Versteegen, Leo and Williams, Ella,
  _A proof of a conjecture of Erdős and Gyárfás on monochromatic path covers_.
  [arXiv:2409.03623](https://arxiv.org/abs/2409.03623).
- [CC26] Chen, Hangdi and Chen, Yaojun, _On monochromatic path covers conjecture of
  Erdős–Gyárfás_. [arXiv:2607.21915](https://arxiv.org/abs/2607.21915), Theorem 1.5.
- [Formal proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos518.lean).
- [Mathlib-walk conversion](https://github.com/AItoBit/erdos518-lean/blob/51892f283436b4dd119eedaf736834ddc953e8bc/Verified518.lean).
-/

@[expose] public section

namespace Erdos518

/--
Is it true that, in any two-colouring of the edges of $K_n$, there exist $\sqrt{n}$ monochromatic
paths, all of the same colour, which cover all vertices?

Pokrovskiy, Versteegen, and Williams [PVW24] proved this for $n > 20^{40}$. Chen and Chen
[CC26] proved it for every positive $n$. The empty graph admits the empty cover.

The two colours are the edges of `G` and `Gᶜ`. Paths may overlap and singleton paths are
allowed. `Nat.sqrt n` is $\lfloor\sqrt{n}\rfloor$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos518-lean/blob/51892f283436b4dd119eedaf736834ddc953e8bc/Verified518.lean#L44"]
theorem erdos_518 : answer(True) ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.HasPathCover (Nat.sqrt n) ∨ Gᶜ.HasPathCover (Nat.sqrt n) := by
  sorry

end Erdos518
