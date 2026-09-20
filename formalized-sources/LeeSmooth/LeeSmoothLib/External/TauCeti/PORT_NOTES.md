# UniversalCover worker report

## Result

Status: **complete** for the 12-file `assigned.json` closure.

The two Chapter 4 existence statements no longer accept a pre-existing topological universal
cover.  They choose a base point from `ConnectedSpace.toNonempty`, instantiate the genuine
TauCeti based-path type `TauCeti.UniversalCover x₀`, use its endpoint projection and covering-map
theorem, and use `TauCeti.UniversalCover.simplyConnectedSpace` for the total space.

The result type now lives in `Type uM`.  This is intentional: the based-path quotient is built in
the source manifold's universe.  The previous independent `uMtilde` result was too strong when
`uMtilde < uM` and would require an impermissible universe-resizing principle.  The independent
universe remains only where harmless, namely in the uniqueness theorem for an already supplied
comparison cover.

The general smooth theorem and its comparison hypotheses now state `IsManifold ... ∞`; no
analytic `ω` conclusion is claimed.  Its atlas is the canonical lifted covering atlas from
`lifted_covering_chartedSpace_isManifold`.

## Topological hypotheses derived

`Corollary_4_43.lean` proves strong local contractibility rather than assuming local path
connectedness or semilocal simple connectedness:

1. Metric balls intersected with a convex model range are contractible.
2. The model-with-corners homeomorphism transports this basis to the model space.
3. Chart partial homeomorphisms transport it to the manifold.
4. Existing genuine instances then supply `LocallyPathConnectedSpace` and
   `TauCeti.SemilocallySimplyConnectedSpace`.
5. Connected plus locally path connected supplies `PathConnectedSpace`.

## Boundary total-space countability and separation

`Exercise_4_45.lean` derives `SecondCountableTopology` for the constructed cover:

1. `C(unitInterval, M)` is second countable, hence each fixed-endpoint `Path` space is second
   countable and its path-homotopy quotient is separable.
2. TauCeti's proved discreteness of that quotient makes every set of fixed-endpoint homotopy
   classes countable.
3. A countable cover of `M` by open, path-connected, path-homotopy-trivial neighborhoods is
   selected from second countability.
4. Every sheet is proved homeomorphic to its base neighborhood using continuity, openness,
   injectivity, and surjectivity of the endpoint projection.
5. The total based-path cover is a countable open cover by these second-countable sheets.

Hausdorffness is not assumed for the total space.  The existing verified
`t2Space_of_isCoveringMap` proof in Proposition 4.41 derives it from the covering map and the
Hausdorff base when packaging `SmoothManifoldWithBoundary`.

## TauCeti port and provenance

- Upstream pin: `7396b87ed870fbaeb387625a7f79a21934cb0312` (`UPSTREAM_PIN`).
- Upstream environment: Lean 4.34-rc2; this worker targets the pinned Lean 4.32.1 environment.
- License: Apache-2.0 (`TAUCETI_LICENSE`).
- All eight copied source files retain their upstream copyright, author, and Apache-2.0 headers.

The 4.32.1 port changes are compatibility-only:

- `Set.mem_ofPred_eq` → `Set.mem_setOf_eq`;
- `Set.ofPred_and` → an explicit set-intersection `change`;
- `ContinuousMap.isOpen_setOfPred_mapsTo` → the current
  `ContinuousMap.isOpen_setOf_mapsTo`;
- `dite_eq_left/right` → `dif_pos/dif_neg`;
- two trailing `rfl` steps removed where 4.32.1 `simp` already closes the goal.

No TauCeti theorem was replaced by a stub or assumption.

## Projective-space endpoints

`Problem_4_10.lean` retains the full canonical sphere-to-real-projective smooth covering proof.
`Problem_4_13.lean` pins `realProjectiveSpaceChartedSpace 2` and
`realProjectiveSpaceIsManifold 2` as local canonical instances, then retains the descended map,
smoothness, immersion, injectivity, compact-source embedding argument, and the final `C^∞`
smooth-embedding conclusion.  It does not expose an arbitrary unrelated projective atlas and does
not weaken the endpoint to a derivative-only statement.

## Verification

Executed the required dependency-closed build (which invokes `./check.sh` once per assigned
source under the shared compiler lock):

```text
$ python3 build_assigned.py
...
ASSIGNED_BUILD_PASS 12
```

`assigned.json` still contains exactly the original 12 files; only its order was normalized to
the dependency order because the local build script recognizes `import` but not Lean's
`public import` lines when computing its topological order.

Only three `unnecessarySimpa` linter warnings were emitted; there were no errors.

The final in-source `#print axioms` commands reported:

```text
'exists_universal_smooth_covering_manifold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'exists_universal_smooth_covering_manifold_with_boundary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'sphere_to_realProjectiveSpace_isSmoothCoveringMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'real_projective_plane_exists_isSmoothEmbedding_to_R4' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

A final source scan found no `sorry`, `admit`, declared `axiom`, `unsafe`, `native_decide`, old
`htop` hypothesis, fake object-file source, or kernel bypass in the assigned Lean sources.
No dependency, toolchain, reference tree, other worker, or git state was modified.
