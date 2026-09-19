# Constructing smooth domains from actual ambient local models

Date: 2026-09-19. Starting from the checked half-collar chart layer.

## Exact input and output

Let N carry its supplied smooth atlas with normed model E, let K be an actual
closed subset with its induced topology, and let I : ModelWithCorners Real E H.
At each p : K, an ambient smooth maximal-atlas chart e is supplied, p belongs
to its source, and e.IsImage K (range I) holds on its actual source.

The theorem exists_smoothClosedDomain_structure constructs a ChartedSpace H K,
IsManifold I infinity K, a smooth embedding of the actual inclusion K -> N,
HasAmbientModelCharts I K and the exact intrinsic-boundary/frontier equality.
No charted or smooth structure on K, immersion of its inclusion, intrinsic
transition regularity or boundary equality is assumed. K's topology is not
replaced. Empty K is covered by a regression test.

## Construction and dependency boundary

Core.ModelDomainChart records exact source/target sets, coordinate maps and
the ambient local set image. Its existence is constructed from e and its
local image relation, not postulated. Separate coordinate and domain lemmas
show the intrinsic extended transitions equal restrictions of genuine ambient
transitions. Ambient maximal-atlas compatibility then produces IsManifold.
A coordinate normal form with complement PUnit proves the inclusion immersion;
the original subtype topology proves it is a topological embedding.

The collar branch proves centers lie in frontier(closure D), obtains regular
openness from actual collar coverage, and constructs ambient product charts
by composing the collar inverse with cross-section and interval coordinates.

## What remains

The current collar-product chart is topological. Its smooth maximal-atlas
membership is NOT automatically supplied to the smooth-domain theorem. The
application to actual surgery geometry still needs genuine smooth collars,
coordinate-model identification, smooth transitions and coverage of all points.
No strong Ricci neck, surgery continuation, finite extinction or terminal
Poincare assertion follows from this layer alone. No full blueprint node is
marked complete merely on the basis of these local results.

## Verification and provenance

All Grok proof submissions were checked after reconstruction into frozen
statements and audited for allowed transitive axioms. Tasks were integrated
only after actual prerequisites; logs and hashes are recorded with commits.
External dependency caches are pinned, not rebuilt from scratch on every task.
This is not independent third-party expert review.
