# Proof-progress checkpoint — 2026-09-20

This commit preserves the currently integrated proof sources and reproducible audit drivers.
It is not a release claiming a complete Poincare formalization or a hole-free Lee library.

## Validation at this checkpoint

- The pinned PoincareConjecture incremental build passes; no cache cleanup was performed.
- The Lee source scan still finds 6 explicit proof holes in 4 files: EuclideanStrictCore (3),
  Theorem 8.49 (1), Problem 4.3 (1), and Problem 5.23 (1).
- The most recent completed targeted Lee regression still reports failures in Proposition 8.15,
  Theorem 5.48, Corollary 6.17, and Problem 6.16. A passing full Lee build is not claimed.
- Individual accepted results have dedicated transitive-axiom audit drivers under package tests.
- Old broad declarations and corrected companion theorems are distinguished in the progress reports.
  Absence of a textual `sorry` is not by itself a proof-completion certificate.

## Included and excluded material

Included: integrated Lean sources, external-source licenses/pins, audit drivers, and progress notes.
Excluded: account/authentication files, local runtime configurations, worker logs, compiled caches,
queue databases, and unfinished candidates in isolated worker directories outside this repository.
Historical progress reports describe the state at their own recording time; later commits supersede
statements there such as “not committed.”

The active proof-worker policy is Codex `gpt-5.6-luna`, with `high`, `xhigh`, or `max` explicitly
selected by task. The current Luna handoff runner is local operational state; the tracked
`tools/lean_swarm` scheduler is a separate, earlier implementation and still needs policy unification.
