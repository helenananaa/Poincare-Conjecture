import PoincareConjecture.ProofContract.Refinement20260927.ApproximateSweepoutTransfer
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- **Math.** Same actual energy/class data as before, but surgery may use
arbitrarily accurate representative transfers instead of one perfect transfer. -/
structure ApproximateIntrinsicProfile (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum continuousEnergy).width 0 ≤ w0
  transfer : ∀ t ∈ events, ApproximateSweepoutTransfer
    ((before t).spectrum continuousEnergy) ((after t).spectrum continuousEnergy) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum continuousEnergy).width s = ((after s).spectrum continuousEnergy).width s ∧
      (d.spectrum continuousEnergy).width t = ((before t).spectrum continuousEnergy).width t ∧
      ∀ r ∈ Ico s t, Nonempty (GoodSweepoutAt (d.spectrum continuousEnergy) r a (3/(4*(r+c))))
/-- **Math.** Regression adapter: every old exact profile is still admissible. -/
def IntrinsicSurvivalProfile.toApproximate {continuousEnergy : SphereEnergyContinuityStatement.{u}}
    {a c w0 T : ℝ} {E : Set ℝ} (W : IntrinsicSurvivalProfile continuousEnergy a c w0 T E) :
    ApproximateIntrinsicProfile continuousEnergy a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  transfer := fun t ht => (W.transfer t ht).toApproximate
  intervals := W.intervals
/-- **Math.** Approximate transfer gives exact downward width jumps; the rest
uses the same class, time interval and previously checked Dini comparison. -/
def ApproximateIntrinsicProfile.toExtinction
    (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (ha : 0 < a) (hc : 0 < c)
    (W : ApproximateIntrinsicProfile continuousEnergy a c w0 T E) :
    ExtinctionProfile a c w0 T E where
  pre := fun t => ((W.before t).spectrum continuousEnergy).width t
  post := fun t => ((W.after t).spectrum continuousEnergy).width t
  initial := W.initial
  terminal_nonneg := ((W.before T).spectrum continuousEnergy).width_nonneg T
  jumps := fun t ht => approximateTransfer_width_le (W.transfer t ht)
  intervals := by
    intro s t hs hst ht hgap
    obtain ⟨d,hg,hstart,hend,hgood⟩ := W.intervals s t hs hst ht hgap
    refine ⟨(d.spectrum continuousEnergy).width,
      intrinsic_width_continuous continuousEnergy compare d.space d.sweepouts d.metric hst.le hg,
      hstart,hend,?_⟩
    intro r hr
    obtain ⟨G⟩ := hgood r hr
    have hrc : 0 < r+c := by linarith [hr.1]
    exact width_dini_of_good_sweepouts checked_near_max checked_minimax_limit
      (d.spectrum continuousEnergy) r a (3/(4*(r+c))) ha
      (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hrc.le)) G
/-- **Math.** Geometry remains RESEARCH. The new jump requirement is weaker
than the old exact transfer, but the existence of controlled flow, good
sweepouts and geometric realizations has not been proved by this declaration. -/
def ApproximateIntrinsicGeometryProducerStatement
    (continuousEnergy : SphereEnergyContinuityStatement.{u}) : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty
            (ApproximateIntrinsicProfile continuousEnergy a c w0 H.horizon H.events))
theorem approximate_producer_of_exact (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (produce : IntrinsicGeometryProducerStatement continuousEnergy) :
    ApproximateIntrinsicGeometryProducerStatement continuousEnergy := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro survive
  obtain ⟨W⟩ := profile survive
  exact ⟨W.toApproximate⟩
theorem width_producer_of_approximate (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (produce : ApproximateIntrinsicGeometryProducerStatement continuousEnergy) :
    WidthControlledGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro survive
  obtain ⟨W⟩ := profile survive
  exact ⟨W.toExtinction continuousEnergy compare ha hc⟩
/-- **Math.** Original frozen public goal. The two regularity leaves are still
explicit; neither they nor the geometric producer are claimed proved here. -/
theorem public_of_approximate_transfer_frontier
    (triangulate : TriangulationProducerStatement.{u}) (atlas : FinitePLAtlasProducerStatement.{u})
    (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (geometry : ApproximateIntrinsicGeometryProducerStatement continuousEnergy) :
    TopologicalPoincareStatement.{u} :=
  public_after_seventeen triangulate atlas
    (width_producer_of_approximate continuousEnergy compare geometry)
#print axioms IntrinsicSurvivalProfile.toApproximate
#print axioms ApproximateIntrinsicProfile.toExtinction
#print axioms approximate_producer_of_exact
#print axioms width_producer_of_approximate
#print axioms public_of_approximate_transfer_frontier
end PoincareConjecture.ProofContract.Refinement20260927
