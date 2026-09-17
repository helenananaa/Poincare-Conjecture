# Integer-deck quotient and the strict-period obstruction

Date: 2026-09-17. Parent: `ec40aa5e837cca7a714af1987ef31748f01227d5`.
This is a local statement audit, not an independent expert or upstream acceptance.

## Concrete quotient, not a placeholder interface

For a space X, a homeomorphism φ : X ≃ₜ X and L : Real, `deck φ L n`
is the homeomorphism (x,t) ↦ (φ^n x, t+nL). `orbitSetoid` quantifies over ALL
integers n and proves reflexivity, symmetry and transitivity.
`Space φ L` is its actual topological quotient, and `proj` is its quotient map.
The continuous and open-map properties are proved by computing the full
saturation of a set as the union of its integer deck translates.

The convention here is q(φ x,t+L)=q(x,t). The blueprint uses
q(x,t+L)=q(φ x,t). `blueprint_endpoint_convention` explicitly uses `Space φ.symm L`
to match that source convention. No silent change of the twist is made.

## Verified geometric statements

For L>0, `proj_injOn_closedStrip` proves injectivity on X × [a,b] when b-a<L.
`proj_injOn_closedStrip_iff` proves necessity as well when X is nonempty.
At one full period, the actual endpoint identification is exhibited.
Open-strip embeddings follow from the proved quotient openness and injectivity.
A short closed strip is embedded by first enlarging it slightly to an open
strip. `closedStripHomeomorphImage` constructs a homeomorphism to its actual
quotient image without assuming that the quotient is Hausdorff.

`image_period_closedStrip` reduces every height by an integer multiple of L.
The full-period closed strip covers the quotient; the image of the corresponding
OPEN strip is dense, not asserted equal to the quotient. Consequently its
closure has empty topological frontier.

A finite open strip disjoint from its first translate has width at most L.
A nonempty frontier of its projected closure rules out equality and yields
b-a<L. `lifted_strip_component_disjoint` derives that disjointness from an
actual `connectedComponentIn` of the inverse image of a quotient region and an
explicit finite-strip identification. It uses maximality of components and the
fact that a bounded strip cannot equal its positive-height translate.
`lifted_strip_component_width_lt` composes these arguments.

## Assumptions that remain explicit and unproved here

For an arbitrary sphere-bundle region in the blueprint, this contribution does
NOT produce the finite lifted-strip description or prove that the image of a
chosen lifted component equals the entire target region.
It does NOT convert an intrinsic smooth boundary statement into a statement
about `frontier (closure D)`, identify every given sphere bundle with this
quotient, or construct the required smooth structures and diffeomorphisms.
The image of a short closed strip is not silently identified with the closure
of an arbitrary target region. Those are separate remaining bridges.
No additional blueprint node is marked complete.

## Validation

Pins stay at Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
Run `python3 tests/check_mapping_torus.py` from the primary package.

The cumulative audit covers 69 declarations: 40 prior declarations and 29 new
ones, including the concrete quotient definitions, not 29 new mathematical
theorems. Every printed transitive axiom set must be contained in
`{propext, Classical.choice, Quot.sound}`.
New tests include the antipodal twist on the actual unit two-sphere, short-strip
injectivity, failure at a full period, a constructed image homeomorphism, the
source-convention adapter, the full-period closure obstruction, and genuine
nonempty-frontier-of-closure witnesses for short sphere cylinders.
The final build starts with no project build artifacts and reuses only the
pinned dependency cache. Local acceptance does not assert upstream acceptance.
