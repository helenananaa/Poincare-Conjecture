# Background gauge and frozen linear PDE frontier — 2026-09-23

18 fixed mathematical goals: nine independent roots, nine dependent consumers. Canonical source is all-cards.json, including direct-import dependency resolution and finite-sum parentheses corrected before affected tasks were enqueued. Do not regenerate from build_cards.py/build_dependents.py without reconciling these changes.

## Mathematical branches
- Global gauge: connection-difference function-linearity, pointwise locality, fiber bilinear realization, and construction of its globally smooth metric trace. Constant-frame metric-trace invariance is proved independently. Applying the trace to the two Levi-Civita connections will require its exact chart coefficient identification.
- Background correction: actual contraction of background connection coefficients, its derivative, its first-order Lie correction, and exact subtraction from the flat-background DeTurck formula. No unknown metric Hessian enters the correction.
- Frozen linear PDE: constant-linear change of coordinates, Hessian contraction, positive diffusion factorization, the bounded-continuous pullback, and an actual local classical IVP for constant positive diffusion coefficients. This is not a variable-coefficient or quasilinear Ricci-flow solver.
- Localization: extend a locally positive self-adjoint C2 metric as a globally uniformly positive field equal to a constant outside compact support; simply cutting the metric off to zero is not sufficient.

All workers use gpt-6-luna, high/xhigh/max, no fallback. Model count unlimited; compilers 6, verifiers 2; one shared Git lock. No duplicate dispatcher. Production acceptance recompiles source and audits transitive axioms. Declaration-only admitted objects remain isolated outside the repo and are never proof evidence.

The V1 root and its six obligations remain unchanged; smoothing and geometric_trace are open. No completion percentage follows from task counts. No full dependency rebuild, remote push or upstream PR was requested.
