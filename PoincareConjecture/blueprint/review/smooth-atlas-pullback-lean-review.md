# Original smooth bundle atlas to cylinder classification

Date: 2026-09-18. Parent: `5a85ceaf925e512a7f68767daed978283afaf6b2`.
The last chat-delivered source base was `01093642d2c53898779ba3bd62a7ca8ac784a069`.
The intermediate covering-pullback commit was found already saved, with matching
source hashes and two successful 328-declaration verification reports. It was
reviewed and reused, not counted as newly authored in this contribution.
This is a local proof and statement audit, not third-party review or priority certification.

## Smooth structures and local assumptions

`CircleSmooth.chartedSpace` is the real local-logarithm atlas on the existing
`AddCircle L` quotient topology. Every local-logarithm transition is proved
locally an affine translation. `CircleSmooth.isManifold` verifies compatibility,
and `coe_isLocalDiffeomorph` proves the actual real quotient projection is locally
smoothly invertible. No global logarithm or continuity of a global representative
choice is asserted. The choice only selects which valid local chart to use.

`IsSmoothBundleChart IB I J e` is a predicate on an actual `Trivialization`:
its forward and inverse maps are smooth on their genuine open domains with the
specified base, total-space and fiber models. It does not contain any desired
pullback property, monodromy, global parametrization or classification result.
The final circle-bundle theorem uses the real local-logarithm atlas for the base
and retains the original supplied total-space and fiber structures.

`contMDiff_projection_of_local_charts` derives smoothness of the actual bundle
projection from this local atlas. This implication is needed: continuity alone
would not make the real height projection of a covering pullback smooth.

## Native pullback compatibility

`contMDiff_pullback_height` uses c composed with real height = original projection
composed with the native `Pullback.lift`. The previously constructed forgetful
local diffeomorphism and the smooth covering map allow smooth lifting.
`isSmooth_pullback_chart` proves both maps of Mathlib's actual `e.pullback c`
smooth in the lifted atlas. Values outside chart domains are never assumed smooth.
`pullback_local_smooth_charts` derives the real-base atlas required by the existing
period-extension theorem. It is no longer an additional pullback assumption.

`abstract_bundle_smooth_real_presentation` composes these results with the natural
smooth deck map and the previously checked integer extension. It constructs a
fiber diffeomorphism and a surjective local diffeomorphism q : F × Real -> TotalSpace,
with fiber injectivity, the base formula and the period formula. Neither q, the
deck map, the cut chart nor the fiber twist is supplied. Nonempty fibers are
derived from the nonempty model fiber by actual bundle charts.

## Region conclusion and retained premises

`abstract_smooth_sphere_bundle_region` directly concludes that closure D is
diffeomorphic to the standard Sphere2 × [0,1]. It requires a Hausdorff actual
sphere bundle, local smooth bundle charts, a positive period, an open nonempty
connected D, a smooth embedded closure with equal finite real dimensions,
image(intrinsic boundary of closure D) = ambient frontier D, and nonempty
fiber-saturated ambient frontier. The total-space model is boundaryless.
The closure's given smooth structure and the usual sphere/interval structures
are retained. Regular-open status is derived, not assumed.

`abstract_smooth_sphere_bundle_boundary_pairing` combines the diffeomorphism with
the two complete boundary components, each an actual original bundle fiber.
It does not assert a prescribed labeling or an extension of an arbitrarily
specified boundary parametrization. The original full blueprint node has not
been re-audited for all alternatives and external interfaces; no new completion
flag is added. None of these statements is a complete Poincare proof.

## Validation

The fixed pins remain Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Run in the primary package:

```bash
lake exe cache get
python3 tests/check_smooth_atlas_pullback.py --fresh
```

The cumulative audit covers 348 declarations: the saved 328 and 20 new entries
(16 theorems, four definitions). It checks 17 suites including an actual standard
sphere bundle with only local-arc charts passed into the presentation theorem.
The new counterexample proves that x -> [abs(x)] is not smooth for the same
standard circle atlas. Thus the original smooth-atlas premise is substantive.
Source hashes are compared before and after validation, and all printed axiom
closures must be subsets of {propext, Classical.choice, Quot.sound}.
Clean primary and separate-source builds reuse only the pinned Mathlib dependency
cache. They are reproducibility checks, not independent third-party verification.
