import PoincareConjecture.ProofContract.Refinement20260927.NormalApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Adds the normal-coordinate route; earlier routes are preserved. -/
structure NormalIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t ∨
          TubularClassTransfer (before t) (after t) t ∨ NormalClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def NormalIntrinsicProfile.toTubular (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (W : NormalIntrinsicProfile.{u} a c w0 T E) :
    TubularIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old | old | raw
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr (Or.inl old))
    · exact Or.inr (Or.inr (Or.inr old))
    · exact Or.inr (Or.inr (Or.inr (normalTransfer_to_tubular split jet inverse raw)))
/-- **Math.** Regression adapter: every older profile remains admissible. -/
def TubularIntrinsicProfile.toNormal {a c w0 T : ℝ} {E : Set ℝ}
    (W : TubularIntrinsicProfile.{u} a c w0 T E) : NormalIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old | old
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr (Or.inl old))
    · exact Or.inr (Or.inr (Or.inr (Or.inl old)))
/-- **Math.** Open research, not an already constructed geometric flow. -/
def NormalGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (NormalIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem tubular_producer_of_normal (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    (produce : NormalGeometryProducerStatement.{u}) : TubularGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toTubular split jet inverse⟩
/-- **Math.** Realization and flow are still explicit research inputs. -/
theorem public_of_normal_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    (geometry : NormalGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_twenty_seven triangulate atlas (tubular_producer_of_normal split jet inverse geometry)
#print axioms NormalIntrinsicProfile.toTubular
#print axioms TubularIntrinsicProfile.toNormal
#print axioms tubular_producer_of_normal
#print axioms public_of_normal_frontier
end PoincareConjecture.ProofContract.Refinement20260927
