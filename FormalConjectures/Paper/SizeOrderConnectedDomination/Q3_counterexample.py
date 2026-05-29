#!/usr/bin/env python3
"""
Counterexample to Mukwembi's Theorem 2.1
(Canad. Math. Bull. 57(1), 2014, pp. 141-144)

The 3-dimensional hypercube Q₃ violates the bound:
    m ≤ (n - γ_c)²/4 + n - 1

Q₃ has n=8, m=12, γ_c=4, so the bound gives 12 ≤ 11, which is FALSE.
"""

from itertools import combinations


def make_Q3():
    """Construct Q₃: vertices = 3-bit strings, edges = Hamming distance 1."""
    vertices = list(range(8))  # 0..7 = 000..111
    edges = [(u, v) for u in vertices for v in vertices
             if u < v and bin(u ^ v).count('1') == 1]
    adj = {v: set() for v in vertices}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return vertices, edges, adj


def is_connected_set(adj, S):
    S = set(S)
    if not S:
        return False
    visited = {next(iter(S))}
    stack = [next(iter(S))]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w in S and w not in visited:
                visited.add(w)
                stack.append(w)
    return visited == S


def is_dominating(adj, n, S):
    S = set(S)
    return all(v in S or (adj[v] & S) for v in range(n))


def gamma_c(adj, n):
    """Compute connected domination number by exhaustive search."""
    for k in range(1, n + 1):
        for S in combinations(range(n), k):
            if is_dominating(adj, n, S) and is_connected_set(adj, S):
                return k, S
    return n, tuple(range(n))


def leaf_number(vertices, edges, adj):
    """Compute Ls = max leaves over all spanning trees."""
    n = len(vertices)
    max_leaves = 0
    best_tree = None
    # Enumerate all subsets of n-1 edges, check if spanning tree
    for tree_edges in combinations(edges, n - 1):
        tree_adj = {v: set() for v in vertices}
        for u, v in tree_edges:
            tree_adj[u].add(v)
            tree_adj[v].add(u)
        if is_connected_set(tree_adj, set(vertices)):
            leaves = sum(1 for v in vertices if len(tree_adj[v]) == 1)
            if leaves > max_leaves:
                max_leaves = leaves
                best_tree = tree_edges
    return max_leaves, best_tree


def draw_ascii_Q3():
    """ASCII art of Q₃ with the counterexample highlighted."""
    print(r"""
    Q₃ = 3-dimensional Hypercube
    ============================

        100 -------- 101
       / |          / |
      /  |         /  |
    110 -------- 111  |
     |   |        |   |
     |  000 ------|- 001
     |  /         |  /
     | /          | /
    010 -------- 011

    Vertices: 8 (3-bit binary strings)
    Edges: 12 (Hamming distance 1)
    Bipartite (even parity / odd parity) → Triangle-free

    """)

    print("    Minimum Connected Dominating Set (γ_c = 4):")
    print(r"""
        100           101
       / |          / |
      /  |         /  |
    110           111  |
     |   |        |   |
     |  [000]-----|-[001]      ← CDS = {000, 001, 010, 011}
     |  /         |  /           (highlighted with [ ])
     | /          | /            Forms a 4-cycle inside Q₃
    [010]------[011]

    This CDS dominates all 8 vertices:
    • 000 → covers 001, 010, 100
    • 001 → covers 000, 011, 101
    • 010 → covers 000, 011, 110
    • 011 → covers 001, 010, 111
    """)

    print("    Why γ_c ≠ 3 (no CDS of size 3 exists):")
    print(r"""
    In Q₃, any connected triple forms a path (no triangles).
    Every path of length 2 misses exactly ONE vertex:

    Path          Misses
    ─────────────────────
    000-001-011   110
    000-001-101   110
    000-010-011   101
    000-100-110   011
    010-110-111   001
    ...           ...

    (All 24 connected triples checked — each misses exactly 1 vertex)
    """)

    print("    The Bound Fails:")
    print("""
    Mukwembi's Theorem 2.1 claims:
        m ≤ (n - γ_c)²/4 + n - 1

    For Q₃:
        m = 12
        (n - γ_c)²/4 + n - 1 = (8 - 4)²/4 + 8 - 1
                               = 16/4 + 7
                               = 4 + 7
                               = 11

        12 ≤ 11  ???  FALSE!
    """)

    print("    Bug in the Paper's Proof (page 143):")
    print("""
    The proof assumes: for some edge uv, γ_c(G) ≤ γ_c(G - {u,v})

    For Q₃, removing ANY pair of adjacent vertices (e.g., 000 and 001)
    gives G' on 6 vertices with γ_c(G') = 2:

        Remove 000, 001 → G' has vertices {010, 011, 100, 101, 110, 111}
        CDS of G': {110, 111} (adjacent, dominate all 6 vertices)
        γ_c(G') = 2 < 4 = γ_c(Q₃)

    So γ_c(G) ≤ γ_c(G') fails: 4 ≤ 2 is FALSE.
    The proof's key inequality is violated for EVERY edge of Q₃.
    """)


def main():
    vertices, edges, adj = make_Q3()
    n = len(vertices)
    m = len(edges)

    print("=" * 60)
    print("COUNTEREXAMPLE TO MUKWEMBI'S THEOREM 2.1")
    print("Canad. Math. Bull. 57(1), 2014, pp. 141-144")
    print("=" * 60)

    draw_ascii_Q3()

    print("=" * 60)
    print("COMPUTATIONAL VERIFICATION")
    print("=" * 60)

    # Basic properties
    print(f"\n  n = {n} vertices")
    print(f"  m = {m} edges")

    # Triangle-free check
    triangle_free = True
    for u, v, w in combinations(vertices, 3):
        e = {(min(a, b), max(a, b)) for a, b in [(u, v), (u, w), (v, w)]}
        if e.issubset(set(edges)):
            triangle_free = False
            break
    print(f"  Triangle-free: {triangle_free}")

    # Connected check
    print(f"  Connected: {is_connected_set(adj, set(vertices))}")

    # Connected domination number
    gc, cds = gamma_c(adj, n)
    print(f"  γ_c = {gc}")
    print(f"  Min CDS: {[bin(v)[2:].zfill(3) for v in cds]}")

    # Verify no CDS of size 3
    cds3_count = sum(1 for S in combinations(vertices, 3)
                     if is_dominating(adj, n, S) and is_connected_set(adj, S))
    print(f"  CDS of size 3: {cds3_count} (exhaustive check)")

    # Bound
    bound = (n - gc) ** 2 / 4 + n - 1
    print(f"\n  Bound: (n - γ_c)²/4 + n - 1 = ({n}-{gc})²/4 + {n}-1 = {bound}")
    print(f"  m = {m} {'>' if m > bound else '≤'} {bound} = bound")
    print(f"  COUNTEREXAMPLE: {m > bound}")

    # Leaf number
    print(f"\n  Computing Ls (max leaves over spanning trees)...")
    ls, best = leaf_number(vertices, edges, adj)
    print(f"  Ls = {ls}")
    print(f"  Ls = n - γ_c? {ls} = {n} - {gc} = {n - gc}: {ls == n - gc}")

    # Check the proof's key assumption for all edges
    print(f"\n  Checking γ_c(G) ≤ γ_c(G-{{u,v}}) for each edge:")
    for u, v in edges:
        # Remove u and v
        remaining = [w for w in vertices if w != u and w != v]
        sub_edges = [(a, b) for a, b in edges if a != u and a != v and b != u and b != v]
        sub_adj = {w: set() for w in remaining}
        for a, b in sub_edges:
            sub_adj[a].add(b)
            sub_adj[b].add(a)
        if is_connected_set(sub_adj, set(remaining)):
            # Remap to 0..len-1 for gamma_c
            remap = {w: i for i, w in enumerate(remaining)}
            n2 = len(remaining)
            adj2 = {remap[w]: {remap[x] for x in sub_adj[w]} for w in remaining}
            gc_prime, _ = gamma_c(adj2, n2)
            status = "✓" if gc <= gc_prime else "✗ FAILS"
            print(f"    Edge {bin(u)[2:].zfill(3)}-{bin(v)[2:].zfill(3)}: "
                  f"γ_c(G') = {gc_prime}  {status}")

    print(f"\n{'=' * 60}")
    print("CONCLUSION: Q₃ is a valid counterexample to Theorem 2.1.")
    print("The paper's proof fails because γ_c(G) > γ_c(G-{u,v})")
    print("for EVERY edge uv of Q₃.")
    print("=" * 60)


if __name__ == "__main__":
    main()
