# helenananaa development fork

This repository preserves upstream `frenzymath/Poincare-Conjecture` history and the local contributions described below. It does **not** claim a complete Lean formalization of the Poincare conjecture or independent expert approval.

## Published baseline: 19 September 2026

- Upstream base: `bb91a091f0b968f8bbe8d861e025a88d82b161be`.
- Local proof baseline: `5e9b6c9eedc1ce152b2f44e6ab31d31396788434` (17 local commits).
- Fixed snapshot branch: `snapshot/20260919-local-proof`.
- Annotated tag: `proof-baseline-20260919`.
- Pins: Lean 4.32.1, Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- Fresh primary-package rebuild, 19 sanity suites, 364 transitive-axiom target audits and the inherited dependency-aware validation gate passed on this date. Dependencies reused the pinned Mathlib cache; this is not an independent fresh build of every upstream reference project.

The additions cover product/fiber saturation, collar and boundary interfaces, real and circle bundle presentations, smooth periodic constructions and complementary frontier selection. Their exact hypotheses and remaining geometric obligations are recorded in `PoincareConjecture/blueprint/review/`.

## Workflow

`main` is the published checked branch. `integration` receives locally verified changes. New fixed-goal worker tasks use isolated worktrees and are merged by the trusted controller, not by agents. The controller never pushes. The owner requested **no upstream pull requests** during this stage; none are part of this setup.

See `tools/lean_swarm/README.md` for the local controller. The acceptance fixtures are engineering tests, not new Poincare milestones. Upstream attribution, source references and Apache-2.0 licensing remain intact.

## Local history preservation

Before reorganization, all nine worktrees, including tracked edits, untracked source/document files, and Git state, were backed up with checksums. A full-history Git bundle was made after completing the shallow clone. Dirty historical worktrees were preserved, not cleaned or overwritten. Most draft files matched the latest baseline; differing README/import-list versions were retained for traceability. A non-ancestor branch is retained in the bundle/local references rather than blindly merged. Cache-provider paths remain in place.

## Attribution

The local contributions are maintained by GitHub user `helenananaa`. They were developed with AI assistance; task design, orchestration and review used ChatGPT, and the parallel worker tests use Codex `gpt-5.6-luna` and Grok `grok-4.6`. Lean checking does not replace expert review of definitions, statement fidelity or mathematical novelty. Do not attribute inherited upstream work to this fork's maintainer.
