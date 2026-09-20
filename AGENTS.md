# Proof project operating rules

## Model policy — latest user instruction, 2026-09-20

- Default provider is Codex, with exact model `gpt-5.6-luna` only.
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
