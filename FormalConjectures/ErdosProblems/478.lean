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

import FormalConjecturesUtil

/-!
# Erdős Problem 478

*References:*
- [erdosproblems.com/478](https://www.erdosproblems.com/478)
- [AnTa16] V. Andrejić and M. Tatarevic, *On distinct residues of factorials*. arXiv:1603.04086
  (2016).
- [GSSV24] Grebennikov, Alexandr and Sagdeev, Arsenii and Semchankau, Aliaksei and Vasilevskii,
  Aliaksei, *On the sequence {$n! \bmod p$}*. Rev. Mat. Iberoam. (2024), 637--648.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [KlMu17] Klurman, Oleksiy and Munsch, Marc, *Distribution of factorials modulo {$p$}*. J. Théor.
  Nombres Bordeaux (2017), 169--177.
- [RoSc60] Rokowska, B. and Schinzel, A., *Sur un problème de {M}. {E}rdős*. Elem. Math. (1960),
  84--85.
- [Tr13] T. Trudgian, *There are no socialist primes less than $10^9$*. arXiv:1310.6403 (2013).
-/

namespace Erdos478

/--
Let $p$ be a prime and $$A_p = \{ k! \pmod{p} : 1\leq k<p\}.$$ Is it true that $$\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?$$
-/
@[category research open, AMS 11]
theorem erdos_478 : answer(sorry) ↔
    Filter.Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (nhds (1 - 1 / Real.exp 1)) := by
  sorry

end Erdos478
