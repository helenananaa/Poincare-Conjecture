import Mathlib

/-!
# Stable outer objects for the Poincare proof, version 1

Only ordinary mathematical data occur here. In particular, neither simple
connectivity nor a sphere recognition conclusion is a field of a manifold.
The Euclidean chart model rules out boundary points. The topology is not changed
when a different smooth atlas is chosen.
-/

universe u

namespace PoincareConjecture.ProofContract.V1
open scoped Manifold ContDiff Topology

abbrev Euclidean3 := EuclideanSpace ℝ (Fin 3)
abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
abbrev Sphere2 := Metric.sphere (0 : Euclidean3) 1

/-- Connectedness of the actual unit three-sphere is proved, not assumed. -/
instance sphere3_connectedSpace : ConnectedSpace Sphere3 := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere ?_ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- Nonempty, compact, connected, Hausdorff, second-countable topological
three-manifolds without boundary, with a specified Euclidean atlas. -/
structure ClosedThreeManifold extends TopCat.{u} where
  hausdorff : T2Space toTopCat
  secondCountable : SecondCountableTopology toTopCat
  compact : CompactSpace toTopCat
  connected : ConnectedSpace toTopCat
  inhabitedSpace : Nonempty toTopCat
  charts : ChartedSpace Euclidean3 toTopCat

instance : CoeSort ClosedThreeManifold.{u} (Type u) := ⟨fun M => M.toTopCat⟩
instance (M : ClosedThreeManifold) : TopologicalSpace M := M.toTopCat.str
instance (M : ClosedThreeManifold) : T2Space M := M.hausdorff
instance (M : ClosedThreeManifold) : SecondCountableTopology M := M.secondCountable
instance (M : ClosedThreeManifold) : CompactSpace M := M.compact
instance (M : ClosedThreeManifold) : ConnectedSpace M := M.connected
instance (M : ClosedThreeManifold) : Nonempty M := M.inhabitedSpace
instance (M : ClosedThreeManifold) : ChartedSpace Euclidean3 M := M.charts

instance (M : ClosedThreeManifold) : LocallyPathConnectedSpace M :=
  ChartedSpace.locallyPathConnectedSpace Euclidean3 M

/-- A smooth atlas on the same underlying topological space; it need not be the
original atlas. Existence of this object is an explicit, unproved obligation. -/
structure Smoothing (M : ClosedThreeManifold) where
  atlas : ChartedSpace Euclidean3 M
  smooth : @IsManifold ℝ _ Euclidean3 _ _ Euclidean3 _ (𝓡 3) ∞ M _ atlas

/-- Smooth manifolds use their existing atlas, not a silently replaced one. -/
abbrev IsSmooth (M : ClosedThreeManifold) : Prop := IsManifold (𝓡 3) ∞ M

/-- Same topological manifold, with the atlas supplied by a smoothing. -/
def Smoothing.manifold {M : ClosedThreeManifold} (s : Smoothing M) :
    ClosedThreeManifold := { M with charts := s.atlas }

instance {M : ClosedThreeManifold} (s : Smoothing M) : IsSmooth s.manifold := s.smooth

/-- Changing the atlas above leaves both the points and topology unchanged. -/
def Smoothing.homeomorph {M : ClosedThreeManifold} (s : Smoothing M) :
    M ≃ₜ s.manifold := Homeomorph.refl M

end PoincareConjecture.ProofContract.V1
