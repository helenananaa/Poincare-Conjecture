# Parallel proof continuation — 2026-09-22

Snapshot: 2026-09-22T13:00:27.128499+08:00
Source: `7684698eab57dedebd6db41e3a60b59781948a81`

29 registry cards represent 28 distinct
mathematical target names. 25 targets are
accepted at this snapshot. Registry counts: {"INTEGRATED": 24, "TIMEOUT": 2, "RUNNING": 2, "QUEUED": 1}.
The bounded-Hessian retry is the original statement via new prerequisites, not
a new target. The reviewed Duhamel result retains its original timeout history.
Task-card proof placeholders are specifications, not accepted Lean declarations.

## Parallelism and real dependencies

All workers use gpt-5.6-luna at explicit high/xhigh/max effort. The model budget
is still unlimited (0). Independent ready cards are dispatched without waiting
for the rest of their depth level. Compiler and verifier stages remain separate;
Git integration remains a single writer. See parallel-observation.json for the
measured peak of in-flight attempts, which includes preparation/verification
rather than pretending to count live model subprocesses.

The bounded-convolution C2 task was too large for its initial attempt. Its new
route proves a shifted Gaussian bound, then a locally uniform integrable
majorant for the kernel and its first two derivatives. That unlocks THREE
independent analytic leaves: first Frechet derivative, derivative of the
gradient integral, and continuity of Hessian integrals. The consumer retains
the exact original statement and does not assume any of those exchanges.

The topology branch constructs radial profiles and their Euclidean lifts in
parallel with chart-supported extension. Their actual composition produces an
ambient coordinate-ball compression. Marked complement transport and shrinking
into a prescribed neighborhood are subsequent concrete consequences.

## Integrity and remaining mathematics

The V1 root and all 13 frozen files are unchanged. Bound leaves remain cover,
handle and sum_factors. Smoothing, the genuine geometric surgery trace, and
sphere-complement recognition remain open. Pulling back an already smooth atlas
is not the existence of a smoothing. Compressing a coordinate ball is not a
relative Schoenflies theorem. Euclidean linear/semilinear kernel estimates are
not a nonlinear closed-manifold Ricci-flow construction.

The Duhamel timeout source needed local proof repairs. The unsupported local
heartbeat override was removed; expensive measurability automation was replaced
with explicit measurable arithmetic and product integration; the empty reverse
interval was handled directly. The original theorem type stayed unchanged and
its accepted term uses only propext, Classical.choice and Quot.sound.

A resource-lock naming issue (compile/compiler and verify/verifier) was found.
A canonical-alias patch passed four isolated semaphore tests but was NOT applied
to the repository after its integration-script write was blocked. No deployment
or resource-controller upgrade is claimed. Existing worker settings remain.
The original remote CI fixture entry also remains unmigrated; no claim of green
remote CI is made. Source builds are targeted, without clearing reference caches.
No remote push or upstream pull request was performed.

See the timestamped validation records for their exact source/name coverage.
The root completion gate must remain nonzero until every mathematical input is
proved. A green freeze gate is not proof completion.
