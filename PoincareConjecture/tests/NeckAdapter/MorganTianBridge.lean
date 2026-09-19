import MorganTianLib.Ch02.EpsilonNeck
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeCollar
import Mathlib.Tactic
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold Riemannian
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [I.Boundaryless] [T2Space N]

/-- Use the actual reference EpsilonNeckStructure.phi, preserving the original
ambient model and topology. Cut sidedness is explicit, not inferred from curvature closeness. -/
theorem reference_epsilonNeckStructure_smoothCollar
    {epsilon : ℝ} (heps : 0 < epsilon)
    (Q : TopologicalSpace.Opens N) [SigmaCompactSpace Q]
    {g : RiemannianMetric I Q} {x : Q}
    (S : MorganTianLib.EpsilonNeckStructure epsilon g x)
    (C : Set N) (c s : ℝ) (hc : c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hs : s = 1 ∨ s = -1)
    (hcut : ∀ z : MorganTianLib.epsilonNeckDomain epsilon,
      (S.phi z : N) ∈ C ↔ s*(z.1.2 0-c) ≤ 0) :
    ∃ Φ : PartialDiffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) I (Sphere2 × ℝ) N ∞,
      Φ.source = (univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0) ∧
      (∀ y : Sphere2, Φ (y,0) =
        (S.phi (scalarToNative (⟨(y,c), ⟨mem_univ _, hc⟩⟩ : scalarNeckDomain epsilon)) : N)) :=
/- SWARM_PROOF_BEGIN -/
by
  exact exists_smoothCollar_of_native_neck_cut I epsilon heps Q S.phi C c s hc hs hcut
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
