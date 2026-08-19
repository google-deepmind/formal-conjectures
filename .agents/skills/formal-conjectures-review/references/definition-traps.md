# Definitions this repository has been burned by

Facts about specific definitions that decided a review. Each entry earned its
place; add to it when a definition surprises you.

- `Nat.Full k n` is `∀ p ∈ n.primeFactors, p ^ k ∣ n`, and `primeFactors 0 = ∅`, so `0` and `1`
  are vacuously Full. `decide` cannot settle it: the `Decidable` instance exists but does not
  reduce, and gets stuck on `List.decidableBAll` over `primeFactorsList`. Use the lemmas in
  `FormalConjecturesForMathlib/Data/Nat/Full.lean`, which ships `Full.zero_right`,
  `Full.one_right` and a `primeFactorsEq` dsimproc, or `norm_num [Nat.Full, Nat.primeFactors,
  Nat.primeFactorsList]`, which needs `set_option maxRecDepth 4000`; the default 512 fails.
- `Finset.Coprime S` is `S.gcd id = 1`, the gcd of the whole set. It is not pairwise, so a set
  containing `1` is coprime whatever else it holds. Before you propose making it pairwise, check
  the source's own example: for Erdős 939 that example is not pairwise coprime, so the change
  would break it.
- `∑' n, f n` is `0` when `f` is not `Summable`, and `0` is rational, an integer, and a limit.
  So `∃ q : ℚ, ∑' n, f n = q` reads as "converges to a rational **or** diverges". `HasSum`
  carries convergence in the statement and does not have this hole. The same applies to
  `Filter.limsup` over `ℝ`, which is `sInf ∅ = 0` on an unbounded sequence. Check which way it
  cuts: inside a bound this weakens the claim, but inside the admissibility predicate of an
  `∃ a, Admissible a ∧ P a` it makes the existential easier to satisfy, and can make a
  `research open` statement provable.
