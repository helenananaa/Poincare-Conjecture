import PoincareConjecture.ProofContract.Refinement20260927.EnergyWidthContinuity
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- **Math.** Replaces the previously assumed interval-width continuity with
quadratic integral data on the same interval and spectrum. Good sweepouts and
actual geometric realization remain separate construction obligations. -/
structure EnergyMinimaxSurvivalProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → SweepoutSpectrum.{u}
  after : ℝ → SweepoutSpectrum.{u}
  initial : (after 0).width 0 ≤ w0
  transfer : ∀ t ∈ events, SweepoutTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ F : SweepoutSpectrum.{u}, Nonempty (QuadraticEnergyRepresentation F s t) ∧
      F.width s = (after s).width s ∧ F.width t = (before t).width t ∧
      ∀ r ∈ Ico s t, Nonempty (GoodSweepoutAt F r a (3/(4*(r+c))))
/-- **Math.** Construct the missing continuity field; all endpoint spectra,
transfers, and good-sweepout certificates are retained without reselection. -/
def EnergyMinimaxSurvivalProfile.toMinimax (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u}) {a c w0 T : ℝ} {E : Set ℝ}
    (W : EnergyMinimaxSurvivalProfile.{u} a c w0 T E) : MinimaxSurvivalProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  transfer := W.transfer
  intervals := by
    intro s t hs hst ht hgap
    obtain ⟨F,⟨d⟩,hstart,hend,hgood⟩ := W.intervals s t hs hst ht hgap
    exact ⟨F,width_continuous_of_quadratic_energy coercive timeUniform hst.le d,hstart,hend,hgood⟩
/-- **Math.** RESEARCH: constructing actual energy representations, good
sweepouts, transfer and controlled surgery is not asserted by this interface. -/
def EnergyControlledGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ,
      0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty
            (EnergyMinimaxSurvivalProfile.{u} a c w0 H.horizon H.events))
theorem minimax_producer_of_energy (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u})
    (produce : EnergyControlledGeometryProducerStatement.{u}) : MinimaxControlledGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toMinimax coercive timeUniform⟩
/-- **Math.** The two NEW compactness leaves have a checked consumer all the
way to the ORIGINAL public goal. Round12 leaves remain explicit until reviewed. -/
theorem public_of_energy_continuity_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (nearMax : UniformNearMaxTaylorStatement)
    (limitPass : MinimaxDiniLimitStatement) (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u})
    (geometry : EnergyControlledGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_sweepout_frontier triangulate atlas nearMax limitPass
    (minimax_producer_of_energy coercive timeUniform geometry)
#print axioms EnergyMinimaxSurvivalProfile.toMinimax
#print axioms minimax_producer_of_energy
#print axioms public_of_energy_continuity_frontier
end PoincareConjecture.ProofContract.Refinement20260927
