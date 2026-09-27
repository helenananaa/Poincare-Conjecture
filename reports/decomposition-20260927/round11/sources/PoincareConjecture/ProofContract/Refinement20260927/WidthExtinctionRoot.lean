import PoincareConjecture.ProofContract.Refinement20260927.ExtinctionBarrier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set CriticalPath.SurgeryBudget
/-- **Math.** Event finiteness uses volume budgets only, BEFORE knowing extinction.
The width comparison is not an input to the volume argument. -/
theorem patch_budget_events_finite (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u})
    {M : ClosedThreeManifold.{u}} [IsSmooth M] (d : MetricInitialData M)
    {B eps : ℝ} (hB : 0 ≤ B) (allowance : NeckAllowance.{u} B eps)
    (H : LocatedProjection checked_epsilon_neck_embedding.{u} M)
    (budget : PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H) : H.events.Finite := by
  have matched := patch_budget_to_matched localDensity assemble M d H budget
  have anchored := matched_budget_to_anchored M d H matched
  have ricci := anchored_neck_to_ricci checked_finite_cap_scaling M d hB allowance anchored
  have uniform := anchored_budget_to_uniform checked_closed_scalar M d ricci
  obtain ⟨a,delta,V,c,ha,hd,samples⟩ := uniform
  exact (finite_event_set_of_measured_histories H.events ha hd samples).1
/-- **Math.** Given the geometric realization of a surviving width, empty end is
now a conclusion. No differentiability or continuity across surgery is assumed. -/
theorem empty_end_of_width_comparison (compare : WidthIntervalComparisonStatement)
    {embed : EpsilonNeckEmbeddingStatement.{u}} {M : ClosedThreeManifold.{u}}
    (H : LocatedProjection embed M) (finite : H.events.Finite)
    {a c w0 : ℝ} (ha : 0 < a) (hc : 0 < c)
    (late : widthPotential a c 0 w0 < 4*a*(H.horizon+c)^((1:ℝ)/4))
    (realize : H.pre H.horizon ≠ [] → Nonempty (ExtinctionProfile a c w0 H.horizon H.events)) :
    H.pre H.horizon = [] := by
  by_contra h
  exact extinctionProfile_impossible compare ha hc H.horizon_pos late finite H.event_times (realize h)
/-- **Math.** Still RESEARCH: actual controlled surgery and min-max geometry must
supply these profiles. Constants are fixed before a requested time horizon;
there is NO empty-end field. The profile is not asserted to be constructed width. -/
def WidthControlledGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ,
      0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (ExtinctionProfile a c w0 H.horizon H.events))
/-- **Math.** Same H for the volume budget and surviving-width profile. Its
empty end is derived, then fed to the previously checked trace reconstruction. -/
theorem geometric_of_width_control (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) (compare : WidthIntervalComparisonStatement)
    (horizons : WidthHorizonStatement) (produce : WidthControlledGeometryProducerStatement.{u}) :
    GeometricTraceStatement.{u} := by
  intro M hsm hsc
  letI : IsSmooth M := hsm
  obtain ⟨d⟩ := metric_initialData_exists M
  obtain ⟨B,a,c,w0,hB,ha,hc,hw0,run⟩ := produce M d hsc
  obtain ⟨T,hT,hlate⟩ := horizons a c w0 ha hc hw0
  obtain ⟨eps,heps,allowance⟩ := checked_uniform_neck_allowance B hB
  obtain ⟨H,hH,budget,width⟩ := run eps heps T hT
  have finite := patch_budget_events_finite localDensity assemble d hB allowance H budget
  have late : widthPotential a c 0 w0 < 4*a*(H.horizon+c)^((1:ℝ)/4) := by simpa only [hH] using hlate
  have hend := empty_end_of_width_comparison compare H finite ha hc late width
  have matched := patch_budget_to_matched localDensity assemble M d H budget
  have anchored := matched_budget_to_anchored M d H matched
  have ricci := anchored_neck_to_ricci checked_finite_cap_scaling M d hB allowance anchored
  exact locatedProjection_trace H hend (anchored_budget_to_uniform checked_closed_scalar M d ricci)
/-- **Math.** Exact original V1 root. No empty-end assumption remains here;
realization of the width estimates and controlled geometry is still RESEARCH. -/
theorem public_of_width_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) (compare : WidthIntervalComparisonStatement)
    (horizons : WidthHorizonStatement) (geometry : WidthControlledGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  Proofs.topological_of_two_contracts
    (smoothing_of_finitePL_producers triangulate (finitePLAtlasProducer_iff.mp atlas))
    (geometric_of_width_control localDensity assemble compare horizons geometry)
#print axioms patch_budget_events_finite
#print axioms empty_end_of_width_comparison
#print axioms geometric_of_width_control
#print axioms public_of_width_frontier
end PoincareConjecture.ProofContract.Refinement20260927
