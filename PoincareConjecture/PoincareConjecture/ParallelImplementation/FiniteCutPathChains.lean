import Mathlib
import Shared.MetricGeometry.LengthSpace

open Set Topology
open scoped ENNReal unitInterval

namespace PoincareConjecture.ParallelImplementation.FiniteCutPathChains

/-!
This module records a local metric fact for pieces cut out of an ambient
pseudo-extended-metric space.  A piece is represented by its actual carrier
subset.  Its intrinsic distance is the infimum of lengths of ambient paths
whose full image lies in that carrier.  This is the subspace path metric:
continuous paths into the subtype are equivalently ambient continuous paths
with image in the subset, and the subtype metric is induced from the ambient
one.

`EmbeddedCollar` is actual topological collar data (an embedding of a product
with the unit interval, based at the specified boundary).  The local estimate
below applies when a collar arc lies in one piece.  It does not construct
finite-crossing paths or identify intrinsic piece distance with ambient
distance.
-/

/-- **Math.** A topological collar embedded in an ambient space, with its zero face
identified with the given boundary subset. -/
structure EmbeddedCollar (X : Type*) [TopologicalSpace X] where
  boundary : Set X
  toFun : {p : X // p ∈ boundary} × I → X
  embedding : Topology.IsEmbedding toFun
  atBoundary : ∀ p, toFun (p, 0) = p.1

namespace EmbeddedCollar

/-- **Math.** A radial arc of the collar, starting at a boundary point and ending at
the corresponding point of the inner collar face. -/
def arc {X : Type*} [TopologicalSpace X] (C : EmbeddedCollar X)
    (p : {x : X // x ∈ C.boundary}) : Path p.1 (C.toFun (p, 1)) where
  toFun t := C.toFun (p, t)
  continuous_toFun := C.embedding.continuous.comp
    (continuous_const.prodMk continuous_id)
  source' := C.atBoundary p
  target' := rfl

@[simp]
theorem arc_zero {X : Type*} [TopologicalSpace X] (C : EmbeddedCollar X)
    (p : {x : X // x ∈ C.boundary}) : C.arc p 0 = p.1 :=
  C.atBoundary p

@[simp]
theorem arc_one {X : Type*} [TopologicalSpace X] (C : EmbeddedCollar X)
    (p : {x : X // x ∈ C.boundary}) : C.arc p 1 = C.toFun (p, 1) := rfl

end EmbeddedCollar

/-- **Math.** A cut piece is specified by its actual carrier subset of the ambient
space.  No path-chain or length estimate is included in this data. -/
structure CutPiece (X : Type*) [PseudoEMetricSpace X] where
  carrier : Set X

namespace CutPiece

/-- **Math.** A point of a cut piece, represented as a point of its carrier subtype. -/
abbrev Point {X : Type*} [PseudoEMetricSpace X]
    (P : CutPiece X) := {x : X // x ∈ P.carrier}

/-- **Math.** Paths which stay in a piece throughout their parameter interval. -/
def ContainedPath {X : Type*} [PseudoEMetricSpace X]
    (P : CutPiece X) (x y : P.Point) :=
  {γ : Path x.1 y.1 // ∀ t : I, γ t ∈ P.carrier}

/-- **Math.** The intrinsic extended distance of a piece: the infimum of ambient
path-lengths over paths entirely contained in the piece.  The empty infimum
is `⊤`, so disconnected points have infinite intrinsic distance. -/
noncomputable def intrinsicEDist {X : Type*} [PseudoEMetricSpace X]
    (P : CutPiece X) (x y : P.Point) : ℝ≥0∞ :=
  ⨅ γ : P.ContainedPath x y, Shared.pathLength (M := X) γ.1

/-- **Math.** Ambient extended distance is bounded above by the intrinsic distance of
the piece.  This records the direction of comparison without conflating the
two metrics. -/
theorem ambientEDist_le_intrinsicEDist {X : Type*} [PseudoEMetricSpace X]
    (P : CutPiece X) (x y : P.Point) :
    edist x.1 y.1 ≤ P.intrinsicEDist x y := by
  unfold intrinsicEDist
  refine le_iInf fun γ => ?_
  exact Shared.LengthSpace.edist_le_pathLength (M := X) γ.1

/-- **Math.** Any ambient path that stays in a piece bounds the piece's intrinsic
distance by its own ambient path length. -/
theorem intrinsicEDist_le_pathLength_of_contained {X : Type*}
    [PseudoEMetricSpace X] (P : CutPiece X)
    {x y : X} (γ : Path x y) (hx : x ∈ P.carrier) (hy : y ∈ P.carrier)
    (hγ : ∀ t : I, γ t ∈ P.carrier) :
    P.intrinsicEDist ⟨x, hx⟩ ⟨y, hy⟩ ≤ Shared.pathLength (M := X) γ := by
  unfold intrinsicEDist
  let q : P.ContainedPath ⟨x, hx⟩ ⟨y, hy⟩ := ⟨γ, hγ⟩
  exact iInf_le
    (fun δ : P.ContainedPath ⟨x, hx⟩ ⟨y, hy⟩ =>
      Shared.pathLength (M := X) δ.1) q

/-- **Math.** In particular, a collar arc contained in one cut piece has intrinsic
length at most its ambient path length. -/
theorem intrinsicEDist_le_collarArcLength {X : Type*}
    [PseudoEMetricSpace X] (P : CutPiece X)
    (C : EmbeddedCollar X) (p : {x : X // x ∈ C.boundary})
    (hArc : ∀ t : I, C.arc p t ∈ P.carrier) :
    P.intrinsicEDist ⟨p.1, by simpa [C.atBoundary p] using hArc 0⟩
        ⟨C.toFun (p, 1), by simpa using hArc 1⟩ ≤
      Shared.pathLength (M := X) (C.arc p) := by
  exact P.intrinsicEDist_le_pathLength_of_contained (C.arc p)
    (by simpa [C.atBoundary p] using hArc 0) (by simpa using hArc 1) hArc

/-- **Math.** The ambient distance and the intrinsic piece distance both lie below
the length of any path contained in that piece. -/
theorem ambientEDist_le_pathLength_of_contained {X : Type*}
    [PseudoEMetricSpace X] (P : CutPiece X)
    {x y : X} (γ : Path x y) (hx : x ∈ P.carrier) (hy : y ∈ P.carrier)
    (hγ : ∀ t : I, γ t ∈ P.carrier) :
    edist x y ≤ P.intrinsicEDist ⟨x, hx⟩ ⟨y, hy⟩ ∧
      P.intrinsicEDist ⟨x, hx⟩ ⟨y, hy⟩ ≤ Shared.pathLength (M := X) γ := by
  exact ⟨P.ambientEDist_le_intrinsicEDist ⟨x, hx⟩ ⟨y, hy⟩,
    P.intrinsicEDist_le_pathLength_of_contained γ hx hy hγ⟩

end CutPiece

end PoincareConjecture.ParallelImplementation.FiniteCutPathChains
