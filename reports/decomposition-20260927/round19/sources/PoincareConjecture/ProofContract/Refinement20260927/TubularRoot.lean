import PoincareConjecture.ProofContract.Refinement20260927.TubularApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** New local tubular entrance; all older transfer entrances remain. -/
structure TubularIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t ∨
          TubularClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def TubularIntrinsicProfile.toRetraction (assemble : TubularInverseAssemblyStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (W : TubularIntrinsicProfile.{u} a c w0 T E) :
    RetractionIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old | raw
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr old)
    · exact Or.inr (Or.inr (tubularTransfer_to_retraction assemble raw))
/-- **Math.** Old profiles acquire no new assumption or construction obligation. -/
def RetractionIntrinsicProfile.toTubular {a c w0 T : ℝ} {E : Set ℝ}
    (W : RetractionIntrinsicProfile.{u} a c w0 T E) : TubularIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr (Or.inl old))
/-- **Math.** Still research: real controlled flow, its local tubular charts,
relative approximating maps, and good sweepout estimates must be constructed. -/
def TubularGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (TubularIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem retraction_producer_of_tubular (assemble : TubularInverseAssemblyStatement.{u})
    (produce : TubularGeometryProducerStatement.{u}) : RetractionGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toRetraction assemble⟩
/-- **Math.** Every pending leaf is an explicit parameter to the same V1 root. -/
theorem public_of_tubular_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (forms : SmoothRetractionFormStatement.{u})
    (assemble : TubularInverseAssemblyStatement.{u}) (geometry : TubularGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_smooth_retraction_frontier triangulate atlas forms (retraction_producer_of_tubular assemble geometry)
#print axioms TubularIntrinsicProfile.toRetraction
#print axioms RetractionIntrinsicProfile.toTubular
#print axioms retraction_producer_of_tubular
#print axioms public_of_tubular_frontier
end PoincareConjecture.ProofContract.Refinement20260927
