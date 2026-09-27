import PoincareConjecture.ProofContract.Refinement20260927.RegularizedRepresentatives
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Old exact/multiplicative transfers are still accepted. A new
alternative supplies actual relative C1 approximation data instead. -/
structure RegularizedIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def ApproximateIntrinsicProfile.toRegularized {a c w0 T : ℝ} {E : Set ℝ}
    (W : ApproximateIntrinsicProfile checked_sphere_energy_continuity.{u} a c w0 T E) :
    RegularizedIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  transfer := fun t ht => Or.inl (W.transfer t ht)
  intervals := W.intervals
def RegularizedIntrinsicProfile.toExtinction
    (relative : RelativeRetractionHomotopyStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (ha : 0 < a) (hc : 0 < c)
    (W : RegularizedIntrinsicProfile.{u} a c w0 T E) : ExtinctionProfile a c w0 T E where
  pre := fun t => ((W.before t).spectrum checked_sphere_energy_continuity).width t
  post := fun t => ((W.after t).spectrum checked_sphere_energy_continuity).width t
  initial := W.initial
  terminal_nonneg := ((W.before T).spectrum checked_sphere_energy_continuity).width_nonneg T
  jumps := by
    intro t ht
    apply additiveTransfer_width_le
    rcases W.transfer t ht with old | regularize
    · exact approximateTransfer_to_additive old
    · exact regularizedClassTransfer_to_additive relative energy regularize
  intervals := by
    intro s t hs hst ht hgap
    obtain ⟨d,hg,hstart,hend,hgood⟩ := W.intervals s t hs hst ht hgap
    refine ⟨(d.spectrum checked_sphere_energy_continuity).width,
      intrinsic_width_continuous checked_sphere_energy_continuity compare
        d.space d.sweepouts d.metric hst.le hg, hstart,hend,?_⟩
    intro r hr
    obtain ⟨G⟩ := hgood r hr
    have hrc : 0 < r+c := by linarith [hr.1]
    exact width_dini_of_good_sweepouts checked_near_max checked_minimax_limit
      (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))) ha
      (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hrc.le)) G
/-- **Math.** Producing the flow, non-null classes, actual approximation maps
and derivative control is still RESEARCH. The old transfer route remains usable. -/
def RegularizedIntrinsicGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty
            (RegularizedIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem regularized_producer_of_approximate
    (produce : ApproximateIntrinsicGeometryProducerStatement.{u} checked_sphere_energy_continuity.{u}) :
    RegularizedIntrinsicGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  exact ⟨H,hH,budget,fun hs => ⟨(Classical.choice (profile hs)).toRegularized⟩⟩
theorem width_producer_of_regularization (relative : RelativeRetractionHomotopyStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (produce : RegularizedIntrinsicGeometryProducerStatement.{u}) :
    WidthControlledGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toExtinction relative energy compare ha hc⟩
/-- **Math.** The two independent approximation leaves have a checked consumer
all the way to the unchanged V1 public goal. This theorem is conditional. -/
theorem public_of_regularization_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (relative : RelativeRetractionHomotopyStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u})
    (geometry : RegularizedIntrinsicGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_seventeen triangulate atlas
    (width_producer_of_regularization relative energy compare geometry)
#print axioms ApproximateIntrinsicProfile.toRegularized
#print axioms RegularizedIntrinsicProfile.toExtinction
#print axioms regularized_producer_of_approximate
#print axioms width_producer_of_regularization
#print axioms public_of_regularization_frontier
end PoincareConjecture.ProofContract.Refinement20260927
