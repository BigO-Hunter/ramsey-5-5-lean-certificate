# ramsey-5-5-lean-certificate

Machine-checked proof of `R(5,5) ≥ 42` in Lean 4 + Mathlib, from an explicit
graph witness.

**Theorem.** `LeapsInBounds.Proofs.Ramsey55.ramsey_5_5_lower_42 :
LeapsInBounds.Ramsey.LowerBound 5 5 42` — i.e. there exists a graph on 41
vertices with no 5-clique and no independent set of size 5. Only the standard
three axioms (`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`.

## Attribution

- **Geoffrey Exoo** — the circulant Ramsey graph `C₄₁(1,2,3,5,8,12,13,16,17,19)`
  (41 vertices, 410 edges, 20-regular; no 5-clique, no independent 5-set).
- **Claude** — witness metadata ("submitted by Claude", notes naming the
  circulant) at `daniel-munro/leaps-in-bounds`,
  `certificates/ramsey/ramsey-5-5-lower-42.g6`, 2026-11-02.
- **daniel-munro** — publisher of the graph6 certificate and the trusted
  statement file `LeapsInBounds/Statements/Ramsey.lean` (copied here
  **verbatim, unmodified**, from `daniel-munro/leaps-in-bounds`,
  toolchain v4.35.0, Mathlib rev `56a005855ea17e0b0958f73ec801ae140b0a1679`).
- **Claude (MultiAgency body)** — this formalization, November 2026.

## Proof method

1. `W` is the circulant with connection set `S = ±{1,2,3,5,8,12,13,16,17,19}`
   on `Fin 41`.
2. A circulant is vertex-transitive: the shift `x ↦ x + t` is an injective
   adjacency-preserving self-map, so any 5-clique moves to one containing
   vertex `0` (generic lemma `no_K5_of_no_badQuad`).
3. A 5-clique containing `0` = `0` + a *bad quadruple* `(a,b,c,d)`. Any bad
   quadruple consists of four neighbors of `0`, so it suffices to check
   quadruples from the 20-element neighbor table `nbrs`
   (`dec_mem_nbrs`, kernel-checked).
4. `no_bad_nbrs` / `no_bad_Sc_nbrs`: the `20⁴ = 160,000` quadruple checks
   (per side) are discharged by kernel evaluation (`decide`).
   The complement graph `Wc` is again a circulant, giving the
   independent-set side.

The framework is generic in `n`, the connection set, and the neighbor table,
so later R(5,5) certificates (43+ bounds, larger circulant witnesses) reuse
the same lemmas with new tables.

## Build

```bash
elan toolchain install leanprover/lean4:v4.35.0   # or let elan resolve lean-toolchain
lake exe cache get   # fetch Mathlib olean cache (~2 GB, ~1 min if cached)
lake build           # ~10-20 min first time incl. kernel checks
```

Output ends with:

```
'LeapsInBounds.Proofs.Ramsey55.ramsey_5_5_lower_42' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## Independent witness check (outside Lean)

`verify_witness.py` decodes `ramsey-5-5-lower-42.g6` with an exact graph6
decoder (upper triangle, column-major, 6 bits/char MSB-first) and exhaustively
verifies no 5-clique / no independent 5-set:

```bash
python3 verify_witness.py ramsey-5-5-lower-42.g6
# VERDICT: R(5,5) >= 42 certified (graph on 41 vertices, clique-free 5 and indep-free 5)
```

## Files

- `LeapsInBounds/Statements/Ramsey.lean` — trusted statement (verbatim from
  daniel-munro/leaps-in-bounds; do not modify)
- `LeapsInBounds/Proofs/Ramsey55.lean` — the certificate proof
- `ramsey-5-5-lower-42.g6` — the graph witness (verbatim from
  daniel-munro/leaps-in-bounds)
- `verify_witness.py` — exact Python decoder/checker

## License

Licensed under the CFSF License — see [LICENSE](LICENSE) ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)); the witness graph is redistributed from daniel-munro/leaps-in-bounds (MIT as published).

---

## Why this repo is up

Reproducible verified bounds: a kernel-checked certificate for R(5,5) ≥ 42 from Exoo's circulant witness — public evidence for independent reruns.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

The certificate check is complete. Open work: independent reruns; R(5,6) and beyond need new witnesses.

