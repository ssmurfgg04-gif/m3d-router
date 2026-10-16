# m3d-router

A C router for the [M3D routing challenge](https://github.com/partcleda/eda-3d-routing-challenge)
(monolithic-3D routing: connect each net's pins across a 3D grid while
minimizing total driver-to-sink path delay under exclusive vertex/edge
capacity).

## method

1. **Negotiated congestion (PathFinder)**: nets route with
   `cost = delay * (1 + history + pres * occupancy)` and iterate, bumping
   history on contested resources, until every vertex and edge is owned by at
   most one net.
2. **Objective-aware tree growth**: each net grows one sink at a time, and an
   attachment minimizes `(alpha * driver-delay-to-attachment) + branch cost`,
   which targets the actual score (sum of driver-to-sink delays) instead of
   generic Steiner weight. `alpha = 0.5` empirically balances directness
   against resource sharing.
3. **Refinement until the budget ends**, alternating:
   - polish sweeps: every net is ripped and re-routed alone against hard
     capacity with a random sink order; kept only if its delay improves
   - LNS batches: random 10-25% of nets ripped and re-routed together

Everything is deterministic per seed, single-threaded C, no dependencies.

## usage

```bash
bash build.sh
./m3droute <case.json> <out.sol.json> [budget-secs] [seed] [alpha]
```

## harness

`.github/workflows/route.yml` routes all 20 intro-tier cases in parallel on
GitHub-hosted runners (one job per case), verifies each solution with the
official checker, and uploads the route files. Heavy computation lives on the
runners, not on any local machine.
