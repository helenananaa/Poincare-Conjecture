import PoincareConjecture.ProofContract.Refinement20260927.SphereEnergySpectrum
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open scoped Manifold ContDiff
/-- **Math.** A concrete target, actual based homotopy class and target metric family.
No free energy field or globally selected tangent frame is stored. -/
structure IntrinsicSpectrumData where
  space : CompactSmoothThree.{u}
  sweepouts : BasedSphereClass space
  metric : ℝ → Riemannian.RiemannianMetric (𝓡 3) space
def IntrinsicSpectrumData.spectrum (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (d : IntrinsicSpectrumData.{u}) : SweepoutSpectrum.{u} :=
  intrinsicSpectrum continuousEnergy d.space d.sweepouts d.metric
/-- **Math.** The analytical profile now uses actual Dirichlet energy. Producing
these classes, good sequences and surgery transfers on the tracked components
remains a research obligation, not a result of this record declaration. -/
structure IntrinsicSurvivalProfile (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum continuousEnergy).width 0 ≤ w0
  transfer : ∀ t ∈ events, SweepoutTransfer
    ((before t).spectrum continuousEnergy) ((after t).spectrum continuousEnergy) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum continuousEnergy).width s = ((after s).spectrum continuousEnergy).width s ∧
      (d.spectrum continuousEnergy).width t = ((before t).spectrum continuousEnergy).width t ∧
      ∀ r ∈ Ico s t, Nonempty (GoodSweepoutAt (d.spectrum continuousEnergy) r a (3/(4*(r+c))))
def IntrinsicSurvivalProfile.toMinimax (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u}) {a c w0 T : ℝ} {E : Set ℝ}
    (W : IntrinsicSurvivalProfile continuousEnergy a c w0 T E) : MinimaxSurvivalProfile.{u} a c w0 T E where
  before := fun t => (W.before t).spectrum continuousEnergy
  after := fun t => (W.after t).spectrum continuousEnergy
  initial := W.initial
  transfer := W.transfer
  intervals := by
    intro s t hs hst ht hgap
    obtain ⟨d,hg,hstart,hend,hgood⟩ := W.intervals s t hs hst ht hgap
    exact ⟨d.spectrum continuousEnergy,
      intrinsic_width_continuous continuousEnergy compare d.space d.sweepouts d.metric hst.le hg,
      hstart,hend,hgood⟩
/-- **Math.** RESEARCH: real flow, matching target components, non-null sweepout
classes, good representatives and surgery transfers must still be constructed. -/
def IntrinsicGeometryProducerStatement (continuousEnergy : SphereEnergyContinuityStatement.{u}) : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty
            (IntrinsicSurvivalProfile continuousEnergy a c w0 H.horizon H.events))
theorem minimax_producer_of_intrinsic (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (produce : IntrinsicGeometryProducerStatement continuousEnergy) : MinimaxControlledGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toMinimax continuousEnergy compare⟩
/-- **Math.** Exact unchanged root with two independent necessary regularity leaves
and three explicit research-level existence obligations. -/
theorem public_of_intrinsic_sphere_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (geometry : IntrinsicGeometryProducerStatement continuousEnergy) : TopologicalPoincareStatement.{u} :=
  public_of_sweepout_frontier triangulate atlas checked_near_max checked_minimax_limit
    (minimax_producer_of_intrinsic continuousEnergy compare geometry)
#print axioms IntrinsicSurvivalProfile.toMinimax
#print axioms minimax_producer_of_intrinsic
#print axioms public_of_intrinsic_sphere_frontier
end PoincareConjecture.ProofContract.Refinement20260927
