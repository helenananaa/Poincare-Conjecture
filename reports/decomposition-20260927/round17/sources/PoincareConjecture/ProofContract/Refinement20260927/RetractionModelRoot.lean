import PoincareConjecture.ProofContract.Refinement20260927.RetractionApproximationData
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** New local retraction entrance; all older transfer entrances remain. -/
structure RetractionIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def RetractionIntrinsicProfile.toRegularized (forms : SmoothRetractionFormStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (W : RetractionIntrinsicProfile.{u} a c w0 T E) :
    RegularizedIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | raw
    · exact Or.inl old
    · exact Or.inr old
    · exact Or.inr (retractionTransfer_to_regularized forms raw)
/-- **Math.** Regression: older profiles acquire no new geometric assumptions. -/
def RegularizedIntrinsicProfile.toRetraction {a c w0 T : ℝ} {E : Set ℝ}
    (W : RegularizedIntrinsicProfile.{u} a c w0 T E) : RetractionIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := fun t ht => (W.transfer t ht).elim Or.inl (fun h => Or.inr (Or.inl h))
/-- **Math.** Still research: actual flow, classes, relative approximation and
local smooth retraction have not been produced by this interface. -/
def RetractionGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (RetractionIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem regularized_producer_of_retraction (forms : SmoothRetractionFormStatement.{u})
    (produce : RetractionGeometryProducerStatement.{u}) : RegularizedIntrinsicGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toRegularized forms⟩
/-- **Math.** Original public target, with every new leaf consumed by a checked parent. -/
theorem public_of_retraction_model_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (forms : SmoothRetractionFormStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u})
    (geometry : RetractionGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_twentyFour triangulate atlas energy (regularized_producer_of_retraction forms geometry)
#print axioms RetractionIntrinsicProfile.toRegularized
#print axioms RegularizedIntrinsicProfile.toRetraction
#print axioms regularized_producer_of_retraction
#print axioms public_of_retraction_model_frontier
end PoincareConjecture.ProofContract.Refinement20260927
