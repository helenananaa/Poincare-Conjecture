import PoincareConjecture.ParallelImplementation.ExteriorCurvatureBound
import PoincareConjecture.ParallelImplementation.CompactCurvatureBound
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.CompactCurvatureOperatorBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
theorem exists_compact_curvature_operator_bound (g : RiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : M,
      MorganTianLib.HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
        (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
          (fun X Y Z p => g.koszulDualSection_dual X Y Z p)) q K :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hcomponents⟩ :=
    _root_.PoincareConjecture.ParallelImplementation.CompactCurvatureBound.exists_compact_uniform_curvature_frame_component_bound g
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * C, ?_, ?_⟩
  · exact mul_nonneg (sq_nonneg _) hC
  · intro q
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y Z p => g.koszulDualSection_dual X Y Z p)
    obtain ⟨a, hqa, hbound⟩ := hcomponents q
    let b := MorganTianLib.orthoFrameBasis g a hqa
    let B := MorganTianLib.curvatureFormAt g g.leviCivitaConnection q
    have hcomp : ∀ i j k l : Fin (Module.finrank ℝ E),
        |B (b i) (b j) (b k) (b l)| ≤ C := by
      intro i j k l
      simpa [B, b, MorganTianLib.orthoFrameBasis_apply] using
        hbound i j k l
    have halg : Riemannian.IsAlgCurvatureForm B :=
      MorganTianLib.isAlgCurvatureForm_curvatureFormAt g
        g.leviCivitaConnection hLC q
    have hop :=
      _root_.PoincareConjecture.ParallelImplementation.ExteriorCurvatureBound.curvatureOperator_bound_of_components
        (d := Module.finrank ℝ E) b halg C hC hcomp
    simpa [MorganTianLib.HasCurvatureOperatorNormLeAt, hLC] using hop
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactCurvatureOperatorBound
