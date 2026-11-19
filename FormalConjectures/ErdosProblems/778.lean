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
# Erdős Problem 778

Alice and Bob alternately colour the edges of $K_n$, Alice red and Bob blue, with Alice moving
first, until every edge is coloured. The problem asks three questions about who has a winning
strategy:

1. Alice wins if her largest red clique is larger than every blue clique. Does Bob win for
   $n \ge 3$?
2. Bob colours two edges after each edge that Alice colours, and Bob wins if his largest blue
   clique is strictly larger than every red clique. Does Bob win for $n > 3$?
3. Alice wins if the maximum degree of the red graph is larger than the maximum degree of the blue
   graph. Who wins?

All three games are instances of the biased game `Clique_{(p,q)}(n)` of [MaSp24]: the first player
claims `p` unclaimed edges per turn and the second player claims `q`, and a player who must move
when fewer edges remain claims all of them. The game is encoded by the finite minimax recursion
`FirstWins`.

*References:*
- [erdosproblems.com/778](https://www.erdosproblems.com/778)
- [Gu83] Guy, R. K., *A miscellany of Erdős problems*. Amer. Math. Monthly 90 (1983), 118-120.
- [MaSp24] Malekshahian, A. and Spiro, S., *On a clique-building game of Erdős*.
  [arXiv:2410.18304](https://arxiv.org/abs/2410.18304) (2024).
-/

@[expose] public section

namespace Erdos778

/-- The edges of the complete graph $K_n$ on `Fin n`. -/
abbrev boardEdges (n : ℕ) : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset

@[category test, AMS 5]
theorem card_boardEdges (n : ℕ) : (boardEdges n).card = n.choose 2 := by
  rw [boardEdges, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/--
`FirstWins n p q win fuel firstToMove red blue` says that the first player can force
`win red' blue'`, where `red'` and `blue'` are the final edge sets of the first and the second
player, starting from the position in which they have claimed `red` and `blue`.

On a turn of the first player (`firstToMove = true`) the first player chooses `min p k` of the
`k` unclaimed edges; on a turn of the second player they choose `min q k` of them. The first
player needs one choice that works, and must win against every choice of the second player.
The game ends when every edge is claimed. Starting with `fuel` equal to the number of edges is
enough when `1 ≤ p` and `1 ≤ q`, because every move then claims at least one edge.

The second player wins exactly when `FirstWins` fails: the game is finite, so the second player
then has a strategy that forces `¬ win red' blue'`.
-/
def FirstWins (n p q : ℕ) (win : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Prop) :
    ℕ → Bool → Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Prop
  | 0, _, red, blue => win red blue
  | fuel + 1, firstToMove, red, blue =>
    let free := boardEdges n \ (red ∪ blue)
    if free = ∅ then win red blue
    else if firstToMove then
      ∃ S ⊆ free, S.card = min p free.card ∧ FirstWins n p q win fuel false (red ∪ S) blue
    else
      ∀ S ⊆ free, S.card = min q free.card → FirstWins n p q win fuel true red (blue ∪ S)

/-- The first player wins the biased game on $K_n$ with `p` edges per first-player turn, `q`
edges per second-player turn, and winning condition `win` for the first player. -/
def BiasedFirstWins (n p q : ℕ)
    (win : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Prop) : Prop :=
  FirstWins n p q win (boardEdges n).card true ∅ ∅

/-- The graph on `Fin n` with edge set `s`. -/
abbrev graphOf {n : ℕ} (s : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))

/-- Alice wins the clique game `Clique(n)`: one edge per turn each, and Alice wins if her
clique number is strictly larger than Bob's. -/
def AliceWinsClique (n : ℕ) : Prop :=
  BiasedFirstWins n 1 1 fun red blue ↦ (graphOf blue).cliqueNum < (graphOf red).cliqueNum

/-- Alice wins the biased clique game `Clique_{(1,q)}(n)`: Bob claims `q` edges per turn, and
Bob wins if his clique number is strictly larger than Alice's. -/
def AliceWinsBiasedClique (q n : ℕ) : Prop :=
  BiasedFirstWins n 1 q fun red blue ↦ (graphOf blue).cliqueNum ≤ (graphOf red).cliqueNum

open scoped Classical in
/-- Alice wins the degree game `Star(n)`: one edge per turn each, and Alice wins if the maximum
degree of her graph is strictly larger than that of Bob's graph. -/
def AliceWinsStar (n : ℕ) : Prop :=
  BiasedFirstWins n 1 1 fun red blue ↦ (graphOf blue).maxDegree < (graphOf red).maxDegree

/-- $K_1$ has no edges, so both players end with the empty graph and Alice does not win. -/
@[category test, AMS 5 91]
theorem not_aliceWinsClique_one : ¬ AliceWinsClique 1 := by
  have h : (boardEdges 1).card = 0 := by rw [card_boardEdges]; rfl
  simp only [AliceWinsClique, BiasedFirstWins, h, FirstWins, lt_self_iff_false,
    not_false_eq_true]

/--
Does Bob have a winning strategy in the clique game on $K_n$ for every $n \ge 3$? Erdős believed
that he does [Gu83].

For $n = 2$ Alice wins by claiming the only edge.
-/
@[category research open, question, AMS 5 91]
theorem erdos_778.parts.i : ∀ n ≥ 3, ¬ AliceWinsClique n := by
  sorry

/--
If Bob claims two edges for each edge that Alice claims, and Bob needs a strictly larger clique
than Alice, does Bob have a winning strategy for every $n > 3$?
-/
@[category research open, question, AMS 5 91]
theorem erdos_778.parts.ii : ∀ n > 3, ¬ AliceWinsBiasedClique 2 n := by
  sorry

/-- The set of $n$ for which Alice wins the degree game on $K_n$. -/
def erdos_778.parts.iii.answer : Set ℕ := sorry

/--
In the degree game Alice wins if the maximum degree of the red graph is larger than the maximum
degree of the blue graph. Who wins?
-/
@[category research open, question value, AMS 5 91]
theorem erdos_778.parts.iii : {n | AliceWinsStar n} = erdos_778.parts.iii.answer := by
  sorry

/--
If Alice wins the clique game on $K_n$ for some $n \ge 2$, then Bob wins it on $K_{n+1}$ and on
$K_{n+2}$ [MaSp24, Propositions 5 and 6].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.clique_succ {n : ℕ} (hn : 2 ≤ n) (h : AliceWinsClique n) :
    ¬ AliceWinsClique (n + 1) ∧ ¬ AliceWinsClique (n + 2) := by
  sorry

/--
If Alice wins the clique game on $K_n$ for some $n \ge 25$, then Bob wins it on $K_{n+3}$
[MaSp24, Proposition 7].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.clique_add_three {n : ℕ} (hn : 25 ≤ n) (h : AliceWinsClique n) :
    ¬ AliceWinsClique (n + 3) := by
  sorry

/--
The set of $n$ for which Bob wins the clique game on $K_n$ has lower density at least $3/4$
[MaSp24, Theorem 1].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.clique_density :
    3 / 4 ≤ {n | ¬ AliceWinsClique n}.lowerDensity := by
  sorry

/--
Bob wins the biased clique game in which he claims four edges per turn, for all sufficiently
large $n$ [MaSp24, Theorem 3].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.biased_four :
    ∀ᶠ n in Filter.atTop, ¬ AliceWinsBiasedClique 4 n := by
  sorry

/--
If Alice wins the degree game on $K_n$ for some $n \ge 3$, then Bob wins it on $K_{n+1}$ and on
$K_{n+2}$ [MaSp24, Propositions 9 and 10].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.star_succ {n : ℕ} (hn : 3 ≤ n) (h : AliceWinsStar n) :
    ¬ AliceWinsStar (n + 1) ∧ ¬ AliceWinsStar (n + 2) := by
  sorry

/--
The set of $n$ for which Bob wins the degree game on $K_n$ has lower density at least $2/3$
[MaSp24, Theorem 2].
-/
@[category research solved, AMS 5 91]
theorem erdos_778.variants.star_density :
    2 / 3 ≤ {n | ¬ AliceWinsStar n}.lowerDensity := by
  sorry

end Erdos778
