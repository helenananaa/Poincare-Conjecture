# Local complementary-closure half-space from a selected genuine collar

Date: 2026-09-19. Partial local topology; no new blueprint completion flag.

## Inputs and outputs

Let X be preconnected, Y a topological space, C a subset of Y, and f an open
embedding of X x (-1,1) into Y with the exact side condition f(x,t) in C iff
 t <= 0. Let D be the actual connectedComponentIn of the complement of C at p.
Assume one central point f(x,0) belongs to frontier D.

`oneSidedCollar_mem_component_iff_pos` derives f(z) in D iff its parameter is
positive. `oneSidedCollar_negative_not_mem_closure` excludes every negative
parameter from closure D; this exclusion does not need preconnectedness or the
frontier-contact assumption. `oneSidedCollar_mem_closure_component_iff_nonneg`
combines both facts with the already checked central-section frontier saturation
to obtain f(z) in closure D iff its parameter is nonnegative.

The negative-side proof uses a genuine open neighborhood contained in C, not
just the fact that an individual point lies outside D. At zero, the existing
frontier saturation lemma is used. The positive side follows from maximality
of the actual complementary connected component.

## Retained obligations

These are conditional theorems about supplied collar data. They do not prove
collar existence, smooth compatibility of a new atlas, global manifold-with-
boundary structure on a complementary closure, strong Ricci neck existence,
or any Ricci-flow analytic theorem. No assertion that every boundary has two
components or that the Poincare conjecture is complete is made.

## Verification and provenance

The three frozen task cards and exact Lean target names are in
`tools/lean_swarm/examples/collar-closure.json`. Luna and Grok produced the two
independent inputs; the dependent closure theorem was generated only after both
inputs had been checked and integrated. The proof statements were fixed before
dispatch. All three targets were independently checked with transitive axioms
contained in {propext, Classical.choice, Quot.sound}.

Initial verification of the producer files uncovered a partial-namespace
artifact-path defect in the controller. After repairing that defect, the same
frozen source bytes passed rechecking; no model rewrite was needed. Both the
original failure and successful recheck are retained in the local task history.
The combined package and earlier tests are checked separately. This is not
independent expert review or a mathematical-priority claim.
