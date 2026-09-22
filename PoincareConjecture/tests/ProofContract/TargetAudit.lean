import PoincareConjecture.ProofContract.V1.Assembly

universe u
open PoincareConjecture.ProofContract.V1
open scoped Manifold ContDiff Topology

/-- The bundled root means exactly the ordinary unbundled assertion. -/
theorem public_target_unbundled : TopologicalPoincareStatement.{u} ↔
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [CompactSpace M] [ConnectedSpace M] [Nonempty M] [ChartedSpace Euclidean3 M]
      [SimplyConnectedSpace M], Nonempty (M ≃ₜ Sphere3) := by
  constructor
  · intro h M _ _ _ _ _ _ _ _
    exact h
      { toTopCat := TopCat.of M
        hausdorff := inferInstance
        secondCountable := inferInstance
        compact := inferInstance
        connected := inferInstance
        inhabitedSpace := inferInstance
        charts := inferInstance }
      inferInstance
  · intro h M hsc
    letI : SimplyConnectedSpace M := hsc
    exact h M

/-- Nonvacuity: the manifold carrier is inhabited by the actual standard sphere. -/
noncomputable def standardSphere : ClosedThreeManifold where
  toTopCat := TopCat.of Sphere3
  hausdorff := inferInstance
  secondCountable := inferInstance
  compact := inferInstance
  connected := inferInstance
  inhabitedSpace := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  charts := inferInstance

example : Nonempty (standardSphere ≃ₜ Sphere3) := ⟨Homeomorph.refl _⟩
example : IsSmooth standardSphere := by
  change IsManifold (𝓡 3) ∞ Sphere3
  infer_instance

/-- A real trace constructor is inhabited; not a trace of an arbitrary manifold. -/
theorem standardSphere_trace : FiniteExtinctionTrace [standardSphere] := by
  apply FiniteExtinctionTrace.step
    (TopologicalStep.discardCovered [] [] standardSphere ?_)
    FiniteExtinctionTrace.empty
  exact ⟨id, isLocalHomeomorph_iff_isCoveringMap.mp
    (Homeomorph.refl Sphere3).isLocalHomeomorph, Function.surjective_id⟩

example : StandardDecomposition standardSphere :=
  standardSphere_trace.decomposes standardSphere (by simp)

#print axioms public_target_unbundled
#print axioms standardSphere_trace
#print axioms TopologicalStep.reconstruct
#print axioms FiniteExtinctionTrace.decomposes
#print axioms recognize_standard_decomposition
#print axioms smooth_topological_of_trace
#print axioms topological_of_smoothing_and_smooth_topological
#print axioms smooth_topological_of_smooth
#print axioms topological_of_contracts
