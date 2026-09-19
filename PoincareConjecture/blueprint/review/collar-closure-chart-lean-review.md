# Explicit open half-collar coordinates for the actual complementary closure

Date: 2026-09-19. Built after the checked collar-closure half-space result.

## Exact statement

The data remain an actual open embedding f : X × (-1,1) → Y, a preconnected
cross-section X, the exact local side relation f(x,t) ∈ C iff t ≤ 0, and a
central point contacting the frontier of D = connectedComponentIn Cᶜ p.
No closure chart, boundary equality or new topology is an input.

`oneSidedCollar_exists_closure_chart` constructs a homeomorphism from
X × [0,1) onto { y : closure D | y ∈ range f }. This target is open in the
actual induced topology on closure D. The forward map is exactly the
restriction of f and the zero parameter maps precisely to frontier D.

## Dependency structure

`CollarFrontierZero` identifies the exact zero section by excluding positive
points using an open neighborhood contained in D. `RestrictOpenEmbedding`
restricts any genuine open embedding to a subspace with an explicit forward
map. `CollarHalfParameter` supplies normalized half-interval coordinates.
`CollarClosureChart` composes the last two homeomorphisms using the previously
checked closure membership identity, then imports the exact frontier result.
The three independent prerequisites and the dependent consumer were assigned
to Grok under frozen statements. The integration queue checked prerequisites
before admitting the consumer.

## Remaining obligations

This is topological, not a claim that the closure already has a smooth atlas.
It does not construct a collar, establish a finite global covering, prove
smooth transition functions, produce strong Ricci necks or discharge the
actual disappearing-component blueprint node. No new blueprint completion
flag is set. For a spherical cross-section, Euclidean local coordinates must
still be composed with the collar chart using the supplied smooth geometry.

## Verification

Four target declarations are independently compiled in the pinned Lean 4.32.1
environment and audited transitively against propext, Classical.choice and
Quot.sound. The fixed dependency cache is reused. This is not third-party
review or a fresh rebuild of all external dependencies.
