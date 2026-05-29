# Counterexample to Mukwembi's Theorem 2.1

**Paper:** S. Mukwembi, *Size, Order, and Connected Domination*, Canad. Math. Bull. **57** (2014), no. 1, 141–144.  
**DOI:** [10.4153/CMB-2013-020-5](https://doi.org/10.4153/CMB-2013-020-5)

---

## The Theorem (as stated in the paper)

> **Theorem 2.1.** Let G be a connected triangle-free graph of order n, size m and connected domination number γ_c. Then
>
> m ≤ (n − γ_c)² / 4 + n − 1,
>
> and this bound is tight.

---

## The Counterexample: Q₃ (3-Dimensional Hypercube)

The 3-cube Q₃ violates the bound.

### Structure of Q₃

```
        100 ———————— 101
       ╱ |           ╱ |
      ╱  |          ╱  |
    110 ———————— 111   |
     |   |        |    |
     |  000 ——————|— 001
     |  ╱         |  ╱
     | ╱          | ╱
    010 ———————— 011
```

| Property | Value |
|----------|-------|
| Vertices | 8 (3-bit binary strings: 000, 001, ..., 111) |
| Edges | 12 (pairs differing in exactly 1 bit) |
| Regular | 3-regular (each vertex has degree 3) |
| Bipartite | Yes (even parity {000,011,101,110} vs odd {001,010,100,111}) |
| Triangle-free | Yes (bipartite ⟹ no odd cycles) |
| Connected | Yes |

### Connected Domination Number: γ_c(Q₃) = 4

A **connected dominating set (CDS)** is a set D such that:
1. Every vertex is in D or adjacent to a vertex in D (dominating)
2. The subgraph induced by D is connected

**Minimum CDS of Q₃** (size 4):

```
        100           101
       ╱ |           ╱ |
      ╱  |          ╱  |
    110           111   |
     |   |        |    |
     |  [000]——————|—[001]       CDS = {000, 001, 010, 011}
     |  ╱         |  ╱           shown with [ ] brackets
     | ╱          | ╱
    [010]————————[011]
```

This CDS forms a 4-cycle inside Q₃ and dominates all vertices:
- 000 → neighbors: 001, 010, **100** [yes]
- 001 → neighbors: 000, 011, **101** [yes]
- 010 → neighbors: 000, 011, **110** [yes]
- 011 → neighbors: 001, 010, **111** [yes]

(Bold = dominated non-CDS vertex)

### Why No CDS of Size 3 Exists

In Q₃, any connected triple must be a path of length 2 (no triangles exist). **Every path of length 2 misses exactly one vertex:**

| Path | Dominates | Misses |
|------|-----------|--------|
| 000 — 001 — 011 | {000,001,010,011,100,101,111} | **110** |
| 000 — 001 — 101 | {000,001,010,011,100,101,111} | **110** |
| 000 — 010 — 011 | {000,001,010,011,100,110,111} | **101** |
| 000 — 100 — 110 | {000,001,010,011,100,110,111} | **011** |
| 010 — 110 — 111 | {000,010,011,100,101,110,111} | **001** |
| ... | ... | ... |

All 24 connected triples checked computationally — **each misses exactly 1 vertex**.  
Therefore γ_c(Q₃) = 4.

### The Bound Fails

```
  Paper's bound: m ≤ (n − γ_c)² / 4 + n − 1

  For Q₃:       m = 12

                (n − γ_c)² / 4 + n − 1
              = (8 − 4)² / 4 + 8 − 1
              = 16 / 4 + 7
              = 4 + 7
              = 11

                12 ≤ 11  [NO]  FALSE
```

---

## Gap in the Paper's Proof

The proof on page 143 is by contradiction on a minimum counterexample G (smallest order n, maximizing size). It has two steps:

### Step 1 (Claim) — Correct

> For any edge uv in G: deg u + deg v ≤ n − γ_c + 2.

This is valid. Since G is triangle-free, the neighborhoods of u and v are disjoint, so the star edges from u and v form a tree T′ with deg u + deg v − 2 leaves. By Lemma 1.2, L(G) ≥ L(T′) = deg u + deg v − 2, and by Eq. (1.1), L(G) = n − γ_c.

### Step 2 — The Error

> "Now let uv be any edge in G such that G′ = G − {u, v} is connected. Then G′ is triangle-free, has order n − 2, and **γ_c(G) ≤ γ_c(G′)**."

This inequality is **asserted without proof and is false**. The proof needs it in exactly this direction to chain:

1. G′ is not a counterexample (by minimality of G), so |E(G′)| ≤ ((n−2) − γ_c(G′))²/4 + (n−2) − 1.
2. Using γ_c(G) ≤ γ_c(G′), substitute γ_c(G′) ≥ γ_c to get (n−2−γ_c(G′))² ≤ (n−2−γ_c)², yielding |E(G′)| ≤ (n−2−γ_c)²/4 + n − 3.
3. Combine with the Claim: m = |E(G′)| + (deg u + deg v) − 1 ≤ (n−2−γ_c)²/4 + n − 3 + (n−γ_c+2) − 1 = (n−γ_c)²/4 + n − 1, contradicting (2.1).

The algebra in step 3 is correct. **The sole error is the monotonicity claim γ_c(G) ≤ γ_c(G′).**

### Failure on Q₃

For every edge uv of Q₃, removing both endpoints gives G′ with γ_c(G′) = 2 < 4 = γ_c(Q₃):

```
  Remove 000, 001  →  G' on {010, 011, 100, 101, 110, 111}

        100 ———— 101
       ╱           |
      ╱            |
    110 ———————  111
     |   ╲       ╱
     |    ╲     ╱
    010 ———— 011

  CDS of G': {110, 111}  →  γ_c(G') = 2

  But γ_c(Q₃) = 4  →  4 ≤ 2 is FALSE  [NO]
```

This happens for **all 12 edges** of Q₃:

| Edge removed | γ_c(G′) | γ_c(G) ≤ γ_c(G′)? |
|--------------|---------|-------------------|
| 000 — 001 | 2 | 4 ≤ 2 [NO] |
| 000 — 010 | 2 | 4 ≤ 2 [NO] |
| 000 — 100 | 2 | 4 ≤ 2 [NO] |
| 001 — 011 | 2 | 4 ≤ 2 [NO] |
| 001 — 101 | 2 | 4 ≤ 2 [NO] |
| 010 — 011 | 2 | 4 ≤ 2 [NO] |
| 010 — 110 | 2 | 4 ≤ 2 [NO] |
| 011 — 111 | 2 | 4 ≤ 2 [NO] |
| 100 — 101 | 2 | 4 ≤ 2 [NO] |
| 100 — 110 | 2 | 4 ≤ 2 [NO] |
| 101 — 111 | 2 | 4 ≤ 2 [NO] |
| 110 — 111 | 2 | 4 ≤ 2 [NO] |

### Why There Is No Monotonicity

One might intuit that removing vertices makes domination harder, since there are fewer vertices available as dominators. But removing vertices **also** reduces the number of vertices that need dominating. For highly regular graphs like Q₃, this second effect dominates: the remaining 6-vertex graph has 7 edges and is dense enough that just 2 vertices suffice as a CDS, while the original 8-vertex graph requires 4. There is **no monotonicity** of connected domination number under vertex deletion — the parameter can go up or down depending on the graph structure.

---

## What Remains True

The other results in the paper are valid and **do not depend on Theorem 2.1**:

| Result | Statement | Status |
|--------|-----------|--------|
| Eq. (1.1) | L(G) = n − γ_c(G) for connected graphs with n ≥ 3 | **True** (well-known identity, formally verified in Lean 4) |
| Corollary 2.2 | L(G) ≥ 2(ᾱ(G) − 1) for triangle-free graphs | **True** (proved from the general conjecture in GraphConjecture2.lean) |
| Corollary 2.3 | L(G) ≥ 4m/n − 2 for triangle-free graphs | **True** (follows from Corollary 2.2) |
| Lemma 1.2 | L(G) ≥ L(T′) for any subtree T′ ≤ G | **True** (formally verified) |

Corollaries 2.2 and 2.3 were proved in the paper via Theorem 2.1, but they actually follow from the **stronger** general conjecture L(G) ≥ 2(ᾱ(G) − 1) for all connected graphs (not just triangle-free), which was proved independently in `GraphConjecture2.lean` using a Fourier–Motzkin argument.

---

## Formal Verification

All claims are formally verified:

| File | What's verified |
|------|----------------|
| `Q3Counterexample.lean` | Q₃ has 12 edges, is triangle-free, γ_c = 4, 12 > 11 (uses `native_decide`) |
| `Q3SafeVerifyTarget.lean` | Target: Mukwembi's bound statement (with `sorry`) |
| `Q3SafeVerifySubmission.lean` | Disproof: self-contained proof of the negation (no `native_decide`) |
| `SizeOrderConnectedDomination.lean` | Lemma 1.2, Eq (1.1), Cor 2.2 and 2.3 |
| `Q3_counterexample.py` | gamma\_c = 4, all triples and edges checked |

### SafeVerify disproof verification

The counterexample has been verified through [SafeVerify](https://github.com/GasStationManager/SafeVerify)'s disproof mode ([PR #16](https://github.com/GasStationManager/SafeVerify/pull/16) by Paul-Lez):

- **Target** (`Q3SafeVerifyTarget.lean`): States Mukwembi's bound `m ≤ (n − γ_c)²/4 + n − 1` for all connected triangle-free graphs, with `sorry` as placeholder.
- **Submission** (`Q3SafeVerifySubmission.lean`): Proves the negation `mukwembi_size_bound.disproof` — there exists a connected triangle-free graph (Q₃) violating the bound. The proof is self-contained and avoids `native_decide`, using `decide` with increased recursion limits so that SafeVerify's `Environment.replay` can verify it.
- **Result**: `SafeVerify check passed.` — all 26 declarations replayed, only standard axioms (`propext`, `Quot.sound`, `Classical.choice`) used.

The `Q3Counterexample.lean` file additionally proves γ_c(Q₃) = 4 formally in Lean 4 by exhaustive case analysis: no singleton, pair, or triple of vertices forms a connected dominating set (`fin_cases` + `native_decide` on all 8 + 64 + 512 cases), and {0,1,2,3} is a CDS of size 4.

### Key Lean 4 theorems

The formal disproof chain in `Q3Counterexample.lean` and `Q3SafeVerifySubmission.lean`:

```
Q3_connectedDominating_four      : Q3.IsConnectedDominating {0,1,2,3}
Q3_connectedDominating_card_ge_four : ∀ D, Q3.IsConnectedDominating D → 4 ≤ D.card
Q3_connectedDominationNumber     : Q3.connectedDominationNumber = 4
Q3_card_edges                    : Q3.edgeFinset.card = 12
Q3_cliqueFree                    : Q3.CliqueFree 3
Q3_violates_bound                : 12 > (8 − 4)²/4 + 8 − 1   (i.e., 12 > 11)
mukwembi_size_bound.disproof     : ∃ G, Connected G ∧ CliqueFree 3 G ∧ ¬(m ≤ bound)
```

All files are in `FormalConjectures/Paper/` and compile against Lean 4 v4.27.0 with Mathlib.

---

## How This Was Discovered

During an attempt to formally prove Theorem 2.1 in Lean 4, an AI agent (Claude) tasked with proving the bound `m ≤ Ls²/4 + n − 1` systematically explored whether the statement was true, and identified Q₃ as a counterexample by testing known graph families (complete bipartite, cycles, hypercubes, Petersen). The counterexample was then verified computationally and formally.
