# Closed seam quotient to real-axis presentation: local review

Date: 2026-09-18. Parent: `1b4e1a145472698fe5e650eadac41a58b611159b`.
This continues the uncommitted bridge sources found in the worktree. All 67
previously audited proof/test files other than the root import were unchanged.
This is a local statement audit, not independent mathematical review.

## Exact scope

`MappingTorus.space_t2Space` proves that the integer-deck quotient is Hausdorff
when the fiber is Hausdorff and the period is positive. This does not follow
from local homeomorphism alone. Unequal circle heights are separated on the
base; equal heights are represented in one injective open product strip.
The result does not require a compact fiber.

`CircleBundle.fundamentalProjection_eq_iff_seam` compares the explicit finite
seam relation with the full integer orbit relation. The inverse twist is
necessary for the convention `(x,L) ~ (phi(x),0)`. No relation is defined as
the kernel of the map being classified.

`CircleBundle.closedRealHomeomorph` retains both original quotient topologies.
For a compact Hausdorff fiber its inverse is continuous by compactness of
the finite cylinder and the independently proved Hausdorff orbit space.
The representative equation and uniqueness of this comparison are proved.

The bundle-derived real presentation is the projection into this orbit space,
followed by the constructed bundle homeomorphism. Its global continuity,
surjectivity, fiberwise injectivity, base-coordinate equation, twisted period
relation, agreement with the finite cut including both endpoints, and local
homeomorphism property are all conclusions, not inputs. No smoothness of the
chosen topological interval trivialization is asserted.

`abstract_sphere_bundle_regular_region` starts with the standard abstract
`FiberBundle Sphere2 E` over `AddCircle L`, a Hausdorff total space and L > 0.
The region is open, nonempty connected, regular open, and has nonempty frontier
whose membership is constant on each actual projection fiber. It concludes
that the actual closure is homeomorphic to the standard closed sphere cylinder.
No monodromy, chosen trivialization, q, or comparison coordinates are inputs.

`abstract_sphere_bundle_smoothClosure_region` instead derives regular openness
from the already verified equal-dimensional smooth embedding and intrinsic
boundary equality. It still concludes a Homeomorph, not a Diffeomorph.
The original total-space topology and supplied smooth structures are retained.

## Remaining obligations

The interval trivialization supplied by the earlier bundle construction is
only topological. A smooth interval trivialization with compatible collar
germs at the two ends is still needed for a smooth real-axis presentation.
Matching values at the endpoints is not a proof that derivatives match there.
The abstract-bundle diffeomorphism conclusion is not claimed, and neither
closed-collar nor full boundary-pairing blueprint completion flags are changed.

## Reproduction and tests

Pins remain Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Run from the main package:

```bash
python3 tests/check_closed_real_bridge.py --fresh
```

The cumulative audit checks 223 declarations (191 previous, 32 bridge entries).
The new suite checks a noncompact Hausdorff fiber; a non-involutive twist and
an intentionally reversed seam; a zero-period counterexample to fiberwise
injectivity; a standard abstract sphere bundle; the upper seam; and the
coordinate-free region interface. The original ten sanity suites are retained.
The verifier rejects warnings, unproved source placeholders and nonstandard
transitive axioms. Source hashes and fixed configuration hashes are recorded.
A separate source directory can run the same script without repository history,
using only the fixed dependency cache; that is not third-party verification.
