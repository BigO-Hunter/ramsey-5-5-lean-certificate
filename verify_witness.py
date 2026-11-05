#!/usr/bin/env python3
"""Exact graph6 decoder + Ramsey witness checker.

Decodes ramsey-5-5-lower-42.g6 (41 vertices, 410 edges) and certifies:
  no 5-clique, no independent set of size 5  =>  R(5,5) >= 42.
Decoder follows the graph6 spec as implemented by networkx: upper triangle
column-by-column, 6 bits per char, MSB first.
"""
import itertools, sys

def decode_g6(path):
    raw = open(path, "rb").read().strip()
    if raw.startswith(b">>graph6<<"):
        raw = raw[10:]
    data = [c - 63 for c in raw]
    n = data[0]
    assert 0 <= n < 63, "only small-header graphs supported"
    data = data[1:]
    bits = []
    for d in data:
        bits += [(d >> i) & 1 for i in (5, 4, 3, 2, 1, 0)]
    need = n * (n - 1) // 2
    assert len(bits) >= need
    adj = [[0] * n for _ in range(n)]
    k = 0
    for j in range(1, n):          # column-major upper triangle
        for i in range(j):
            adj[i][j] = adj[j][i] = bits[k]
            k += 1
    return n, adj

def has_kclique(adj, n, k):
    for comb in itertools.combinations(range(n), k):
        if all(adj[a][b] for a, b in itertools.combinations(comb, 2)):
            return comb
    return None

def main():
    n, adj = decode_g6(sys.argv[1] if len(sys.argv) > 1 else "ramsey-5-5-lower-42.g6")
    deg = [sum(r) for r in adj]
    print(f"n={n} edges={sum(deg)//2} degrees={sorted(set(deg))}")
    # circulant structure on natural order
    S = sorted({(j - i) % n for i in range(n) for j in range(n) if i != j and adj[i][j]})
    circ = all(bool(adj[i][(i + d) % n]) == ((d in set(S) and adj[i][(i + d) % n] == 1))
               for i in range(n) for d in S)
    full_circ = all(adj[i][(i + d) % n] == 1 for i in range(n) for d in S) and \
                all(adj[i][(i + d) % n] == 0 for i in range(n) for d in range(1, n) if d not in S)
    print(f"connection set S = {S}")
    print(f"|S|={len(S)} symmetric={all((-d) % n in set(S) for d in S)} 0-in-S={0 in set(S)} circulant={full_circ}")
    c5 = has_kclique(adj, n, 5)
    comp = [[1 - adj[i][j] for j in range(n)] for i in range(n)]
    i5 = has_kclique(comp, n, 5)
    print("5-clique:", c5)
    print("independent 5:", i5)
    if c5 is None and i5 is None:
        print("VERDICT: R(5,5) >= 42 certified (graph on 41 vertices, clique-free 5 and indep-free 5)")
    else:
        print("VERDICT: WITNESS FAILS")
        sys.exit(1)

if __name__ == "__main__":
    main()
