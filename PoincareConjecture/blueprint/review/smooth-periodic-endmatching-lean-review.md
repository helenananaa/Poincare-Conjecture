# Smooth periodic end matching: local statement review

Date: 2026-09-18. Parent: `c92c159e8aa790d53ae64c8dfd561f7958a9f1b7`.
This is a local proof/statement audit, not independent expert approval.

## Inputs and outputs

The input is a continuous real-base projection p : M -> Real with local
smooth bundle trivializations in the given smooth structures, a positive
period L, and a GIVEN diffeomorphism T of M satisfying p(T z) = p(z) + L.
The main theorem constructs a smooth trivialization k covering [0,L],
a positive radius epsilon with 2*epsilon < L, and a fiber diffeomorphism phi.
Both complete end collars lie in k.baseSet. On |t| < epsilon its inverse obeys

    k.symm (t+L, x) = T (k.symm (t, phi x)).

The inverse chart is proved to be a local diffeomorphism at every point of
its open target. No forward-only smoothness assumption substitutes for an inverse.
The total-space and fiber smooth structures are never replaced or transported.

Main entry: `SmoothBundle.exists_smooth_endmatched_period_chart`.
All names are under `PoincareConjecture.Topology.FiberSaturation`.

## Construction

The previous interval theorem supplies an initial smooth chart e. A second
chart is obtained by transporting e with T and translation of the base.
A splice just before L leaves the initial chart unchanged near zero.
The parameter clamp freezes beyond the splice collar, so near L the correction
is ONE fixed fiber diffeomorphism, not a time-dependent family. Its inverse is
the twist in the inverse-chart identity. All collar radii are constructed from
openness and L > 0; endpoint matching is not an extra input.

## What is not proved here

The smooth deck transformation T is an input. Constructing the smooth pullback
atlas and this T from an arbitrary abstract smooth circle bundle remains an
integration obligation. This theorem does not replace that obligation with a
new definition, and it does not assert a smooth all-real periodic extension.
The latter also requires gluing the integer translates and proving smoothness
at every seam. No complete Poincare proof or additional blueprint completion
flag is claimed.

## Checks

Use the unchanged Lean 4.32.1 and Mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
Run `python3 tests/check_periodic_endmatching.py --fresh` in the primary package.
The cumulative audit expects 265 declarations (250 old, 15 new), with axioms
contained in {propext, Classical.choice, Quot.sound}. It rejects placeholders,
nonstandard native reduction axioms, compiler warnings, and changing source hashes.
The new examples include a time-dependent shear, a two-chart local atlas neither
member of which covers [0,4], the genuine unit two-sphere, a non-involutive fiber
translation, and a proof that using its forward twist instead of its inverse fails.
A second source copy uses the same pinned Mathlib dependency cache but no project
build artifacts; it is reproducibility testing, not third-party verification.
