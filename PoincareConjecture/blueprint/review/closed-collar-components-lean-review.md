# Closed collar components: verified topological interfaces

Date: 2026-09-17. Previous local commit: `6d0ba6da449cb07d670a914c11b06faea742d6ca`.
This is a local statement-alignment review, not independent expert or upstream approval.

## What is proved

The main new declaration is `sphere_closed_collar_saturation` in namespace
`PoincareConjecture.Topology.FiberSaturation`. For an embedding
`f : Sphere2 × Icc a b → Y`, an open ambient region D and
`∃ T, f ⁻¹' frontier D = univ ×ˢ T`, it proves:

* Each component meeting the open collar is the image of a full-fiber
  cylinder with a nonempty open order-connected real base A contained in `(a,b)`.
  The component is the actual `connectedComponentIn (D ∩ range (collarInteriorMap f))`.
* Every closed-collar fiber, including both endpoints, is wholly in D,
  wholly in the ambient frontier of D, or wholly outside its ambient closure.
* The relative frontier of each pulled-back component is fiber-saturated.

`collar_component_frontier_subset_ambient` additionally proves that this
relative frontier maps into the original ambient frontier of D.
There is no new assumption that a component's frontier already has that property.

The intermediate proofs use connectedness of each fiber, the precise formula
for connected components of a cylinder, local connectedness of the real base,
and preservation of relative components by embeddings. The ambient map need not
be open at a closed-collar endpoint. The fiber is the actual sphere in R^3.
No global connectedness of D, compact closure of D, or smoothness is needed for
these stronger topological statements.

## Scope boundary

The blueprint node `lem:closed-collar-fiber-saturation` remains `notready`.
The new theorem proves whole-fiber membership in the ambient frontier, but
has not yet proved that an endpoint fiber is an entire connected component
of the ambient frontier. That requires formalizing the finite disjoint
family of displayed boundary spheres, including its separation properties,
not just saturation of the pullback inside a single collar.

No smooth collar classification, mapping-torus branch, surgery reconstruction
or complete Poincare theorem is claimed. Existing blueprint completion flags
are unchanged. The older `fiber-saturation-lean-review.md` records the previous
stage and should be read together with this extension.

## Validation

The dependency pins remain Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
From the primary package directory run:

```bash
python3 tests/check_closed_collar.py
```

This runs the upstream package validator, both regression and new concrete
sphere-collar sanity checks, and a combined audit of 31 named declarations
(16 from the previous stage plus 15 new theorems). Each transitive axiom set
must be contained in `{propext, Classical.choice, Quot.sound}`. The verifier
also rejects incomplete proof placeholders, compilation warnings and native
unchecked decision shortcuts in the contributed Lean source.
