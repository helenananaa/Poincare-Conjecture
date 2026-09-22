# Regularity and marked sphere-complement frontier — 2026-09-22

Snapshot: 2026-09-22T13:44:02.454169+08:00
Source: `1b9b311e7e17e954d4aefeb74c64b56d4a81c2ce`

New registry cards: 14. Statuses: {"INTEGRATED": 12, "QUEUED": 1, "RUNNING": 1}.
The three previously running C2 endpoints completed before this batch; they are
not included in the new-card total. OriginalBoundedC2Audit20260922.lean verifies
the old complete statement against the new assembled proof, without extra
assumptions or a weaker conclusion.

## Mathematical scope

The analysis branch consumes the actual bounded-data C2 convolution theorem.
Its new goals are estimates for actual Hessian entries, their Holder spatial
modulus, an integral coefficient-freezing error and its time-integrated bound,
and a true second-order product localization identity. These are not merely
formal expressions for unproved derivatives.

The positive-time branch proves an exact HasDerivAt kernel formula, a uniform
Gaussian bound over a compact time-space set, then a real integrable time
majorant, and finally the equation for the actual bounded-data convolution.
The IVP goal allows bounded uniformly continuous data, without imposing the
previous smooth/compact-support condition. Its exact conclusion is spatial C2
at each positive time, HasDerivAt in time satisfying the equation, and a uniform
initial trace. Do NOT infer an explicitly proved jointly smooth solution or
joint C1 regularity from the short docstring label alone.

The topology branch uses real hemispheres and the equator of the unit sphere.
The marked complement consumer ASSUMES an ambient homeomorphism that sends the
removed ball to an open hemisphere. The existence of such a straightening for
an arbitrary coordinate ball is NOT supplied. This conditional result cannot
be bound as a solution of SphereComplementBallStatement.

## Verification and limits

Only source passing the frozen task-template comparison, independent Lean
compilation and standard transitive-axiom checks is integrated. The extra
production revalidation report identifies its exact snapshot/name coverage.
The live root guard and original-fixture plus multi-binding regression tests
are recorded separately. A task specification may contain a deliberate proof
placeholder; it is not evidence that any accepted Lean source has such a hole.

No V1 definition, target or lock was changed. The public proof remains open:
smoothing, a genuine geometric surgery/extinction trace, and general sphere
complement recognition are not proved. The old remote CI fixture entry and the
previously isolated resource-alias patch have not been silently modified here.
No remote push or upstream pull request was performed.

## Task snapshot

| Task | State | Exact declaration |
|---|---|---|
| reg-equator-sphere | INTEGRATED | `PoincareConjecture.ProofContract.Proofs.equator_homeomorph_sphere2` |
| reg-hemisphere-frontier | INTEGRATED | `PoincareConjecture.ProofContract.Proofs.upper_hemisphere_frontier` |
| reg-lower-hemisphere-ball | INTEGRATED | `PoincareConjecture.ProofContract.Proofs.lower_hemisphere_homeomorph_ball` |
| reg-round-complement-marked | INTEGRATED (conditional on ambient straightening) | `PoincareConjecture.ProofContract.Proofs.round_coordinate_complement_recognition` |
| reg-actual-hessian-bound | INTEGRATED | `MorganTianLib.ParabolicPDE.actual_heat_hessian_holder_bound` |
| reg-bounded-classical-ivp | QUEUED | `MorganTianLib.ParabolicPDE.bounded_uniformly_continuous_heat_ivp` |
| reg-bounded-classical-time | RUNNING | `MorganTianLib.ParabolicPDE.bounded_heat_time_equation` |
| reg-coefficient-commutator | INTEGRATED | `MorganTianLib.ParabolicPDE.heat_hessian_coefficient_commutator` |
| reg-hessian-holder-space | INTEGRATED | `MorganTianLib.ParabolicPDE.actual_heat_hessian_spatial_holder` |
| reg-integrated-coefficient-error | INTEGRATED | `MorganTianLib.ParabolicPDE.integrated_coefficient_freezing_error` |
| reg-localization-product | INTEGRATED | `MorganTianLib.ParabolicPDE.laplacian_cutoff_product_rule` |
| reg-time-derivative-dominator | INTEGRATED | `MorganTianLib.ParabolicPDE.euclideanHeatKernel_time_derivative_dominator` |
| reg-time-formula | INTEGRATED | `MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_time_formula` |
| reg-time-space-kernel-bound | INTEGRATED | `MorganTianLib.ParabolicPDE.euclideanHeatKernel_compact_time_space_bound` |
