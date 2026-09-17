# Fiber saturation: statement alignment and validation

Date: 2026-09-17. Base revision: `bb91a091f0b968f8bbe8d861e025a88d82b161be`.
This is a contribution-local statement audit, not independent expert approval.

## Scope

The declaration `PoincareConjecture.Topology.FiberSaturation.fiber_saturation_from_spherical_frontier`
implements both clauses of `lem:fiber-saturation-from-spherical-frontier`.
It is imported by the primary package root, not an isolated companion project.

`Sphere2` is `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.
Its connected-space instance is proved using Mathlib's sphere connectedness theorem.
`FiberSaturated (frontier U)` quantifies over every point of each actual product fiber.
No substitute boundary operator or analytic assumption is introduced.

The ambient type is `Sphere2 × J`, with `J` the subtype of an open real set.
Thus both `closure U` and `frontier U` have exactly the relative topology of the blueprint.
The conclusion `A.OrdConnected` says that every real interval between two points of A lies in A.
Together with `IsOpen A`, this is the open-interval property (including the empty and unbounded cases).
The premise uses `IsPreconnected U`, so empty regions are not excluded by a stronger hypothesis.
If U is nonempty, its product description makes A nonempty as well.
The compact clause assumes nonempty frontier and derives the necessary nonemptiness internally.
Since J is open, the conclusions `a ∈ J` and `b ∈ J` place the endpoints in its interior.
The strict inequality `a < b` ensures the two endpoint fibers are distinct and disjoint.

The Lean result needs only openness of J, not order-connectedness or nonemptiness of J.
It therefore also applies to every nonempty open interval in the blueprint.

## Additional interfaces, not additional completed blueprint nodes

`exists_closed_cylinder` describes the relative closure by the closed parameter interval.
`neck_coordinates_cylinder` transports the open region, its closure, and its frontier
through a supplied genuine homeomorphism to product neck coordinates.
Neither result constructs a smooth collar or proves the mapping-torus alternative.
In particular, `lem:closed-collar-fiber-saturation` and
`lem:relative-fiber-boundary-pairing` remain unmarked.

## Reproduction

Use the existing package pins: Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. No dependency pin is changed.
From the `PoincareConjecture` package directory:

```bash
lake exe cache get
lake build
lake env lean tests/FiberSaturationSanity.lean
lake env lean tests/FiberSaturationAudit.lean
```

The audit prints the transitive axioms of sixteen declarations. Each set must
be contained in `{propext, Classical.choice, Quot.sound}`.
The sanity file checks an actual sphere cylinder, including compact closure,
and instantiates the first blueprint clause for an empty open region.
All assertions are verified by Lean; no project proof is supplied by a stub.
The historical 2026-08-24 route review remains a historical document, not an
updated claim that the other 278 blueprint nodes have been formalized.
