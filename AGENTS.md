# Proof project operating rules

## Model policy — latest user instruction, 2026-09-23

- Default provider is Codex, with exact model `gpt-6-luna` only.
- Explicitly pass both the model and reasoning effort on every invocation.
- Allowed reasoning efforts: `high`, `xhigh`, `max`. Never select lower levels.
- Use high for integration repairs, xhigh for substantial proofs, max for hard foundations.
- Grok quota is exhausted: no new Grok calls, retries, or automatic provider fallback.
- Do not launch SOL or another model. Failure must be surfaced, not silently rerouted.
- Preserve Grok source checkpoints and logs; recompile source rather than trust old object files.
- Keep local Lean compilation resource-bounded independently of model concurrency.

## Proof and repository integrity

- Preserve prior work. A stopped worker's file is a candidate, not an accepted proof.
- Recompile candidates with the pinned Lean/Lake options before integration.
- Audit transitive axioms; no proof-hole shortcuts, new axioms, kernel bypasses, or fabricated compiled modules.
- Document necessary mathematical statement corrections. Never assume the target conclusion to remove a sorry.
- Do not modify the verified Poincare mainline or blueprint completion markers for these Lee cleanup tasks.
- Do not commit, push, or open an upstream pull request without an instruction to do so.

## Critical-path priorities — 2026-09-20 continuation

- Track end-to-end Poincare completion separately from Lee-library cleanup and textual sorry counts.
- Prioritize usable theorem dependencies, mathematical prerequisites and reproducible integration repairs.
- Do not repeat accepted PBW or ambient Sard proofs; consume the verified source checkpoints.
- A general Ado relaunch needs a materially new accepted prerequisite or a specific independent subproblem, not the unchanged broad prompt.
- Counterexamples invalidate a specification; preserve them and prove the correct statement rather than silently add the conclusion as a premise.
- Do not spend another agent on a mere rewrite of an already supplied frontier equality or an already proved bundle theorem.
- New mainline bridges stay in isolated workspaces until compilation, statement review and transitive-axiom checks pass.
- Task reports and newly created imports are not proof-completion evidence. Record conditional, unconditional, refuted and pending statements separately.

## Unified scheduler — latest architecture request

- Luna model concurrency and default dispatcher budget are unlimited (0). No fixed 8/32 cap.
- New fixed proof tasks use tools/lean_swarm/cli.py, explicit high/xhigh/max and the shared dependency registry. Do not restart old handoff jobs to bypass the queue.
- Running research workers are adopted without interruption; returned source snapshots require independent target-axiom verification and explicit semantic review.
- Compiler/verifier resource limits remain independent of model concurrency. Never grant a worker write access to the full trusted scheduler state directory.
- Auto-integration is allowed only for accepted fixed statements; research acceptance gates require a reviewed manifest matching an actual integration commit. No automatic upstream push.

## Frozen public proof boundary — V1, 2026-09-22

- The public goal and recursive topology interface live in `PoincareConjecture.ProofContract.V1`.
- Run `python3 tools/proof_contract/check.py` before integration. Do not edit/re-hash V1 frozen files to make a task pass.
- Implement leaf proofs in new modules outside the immutable V1 files; bind the exact theorem in `docs/proof-contract/v1.bindings.json` and run the `--lean` audit.
- Conditional assembly, declarations of Props, interface counts, and green freeze CI are not Poincare completion. `--lean --require-complete` must pass before any completion claim.
- The topological public target and the smooth diffeomorphism target remain distinct. Do not mark the old blueprint target `leanok` from the conditional assembly.
- `GeometricTraceStatement` is an open, concrete output obligation, not an already constructed Ricci flow. Its internal PDE/flow/surgery definitions are not claimed frozen. Preserve the V1 output while refining that subtree.
- The existing model/provider and resource policies above are unchanged.
