import PoincareConjecture.ProofContract.Refinement20260927.AcceptedForty
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff
/-- **Math.** The actual C1 representatives generate the old ambient data, with identical references. -/
theorem c1ClassTransfer_to_ambient (bound : C1AmbientFrameBoundStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement)
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : C1ClassTransfer source target t) :
    AmbientClassTransfer source target t := by
  intro i
  obtain ⟨r,hr⟩ := h i
  obtain ⟨j,hj⟩ := r.toJoint checked_c1_density_continuity bound (target.metric t)
  obtain ⟨out,hout⟩ := j.toAmbient (cylinder_c1_after_uniform restrict extend)
  refine ⟨out,?_⟩
  intro s
  rw [hout,hj]
  exact hr s
/-- **Math.** No geometric flow is asserted by this profile data. -/
structure C1IntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t ∨
          TubularClassTransfer (before t) (after t) t ∨ NormalClassTransfer (before t) (after t) t ∨ EmbeddingClassTransfer (before t) (after t) t ∨ AmbientClassTransfer (before t) (after t) t ∨ C1ClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
/-- **Math.** Preserve all prior seven transfer entrances; add C1 transfer as the eighth. -/
def C1IntrinsicProfile.toAmbient (bound : C1AmbientFrameBoundStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement)
    {a c w0 T : ℝ} {E : Set ℝ} (W : C1IntrinsicProfile.{u} a c w0 T E) :
    AmbientIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with h | h | h | h | h | h | h | h
    · exact (Or.inl h)
    · exact (Or.inr (Or.inl h))
    · exact (Or.inr (Or.inr (Or.inl h)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (c1ClassTransfer_to_ambient bound restrict extend h)))))))
/-- **Math.** Every old ambient profile remains admissible without new hypotheses. -/
def AmbientIntrinsicProfile.toC1 {a c w0 T : ℝ} {E : Set ℝ}
    (W : AmbientIntrinsicProfile.{u} a c w0 T E) : C1IntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with h | h | h | h | h | h | h
    · exact (Or.inl h)
    · exact (Or.inr (Or.inl h))
    · exact (Or.inr (Or.inr (Or.inl h)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
/-- **Math.** Open research: controlled trace and good sweepouts, with explicit C1 transfer. -/
def C1GeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (C1IntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem ambient_producer_of_c1 (bound : C1AmbientFrameBoundStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement)
    (produce : C1GeometryProducerStatement.{u}) : AmbientGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toAmbient bound restrict extend⟩
/-- **Math.** Actual connection to the unchanged V1 root; controlled flow still must be produced. -/
theorem public_of_c1_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (bound : C1AmbientFrameBoundStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement)
    (geometry : C1GeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_thirty_eight triangulate atlas (ambient_producer_of_c1 bound restrict extend geometry)
#print axioms c1ClassTransfer_to_ambient
#print axioms C1IntrinsicProfile.toAmbient
#print axioms AmbientIntrinsicProfile.toC1
#print axioms ambient_producer_of_c1
#print axioms public_of_c1_frontier
end PoincareConjecture.ProofContract.Refinement20260927
