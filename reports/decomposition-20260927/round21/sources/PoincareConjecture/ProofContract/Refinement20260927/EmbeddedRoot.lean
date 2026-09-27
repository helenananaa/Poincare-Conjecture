import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** The embedding-only entrance is additional; all older routes remain. -/
structure EmbeddingIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t ∨
          TubularClassTransfer (before t) (after t) t ∨ NormalClassTransfer (before t) (after t) t ∨ EmbeddingClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def EmbeddingIntrinsicProfile.toNormal (coordinates : EmbeddedNormalCoordinatesStatement.{u})
    {a c w0 T : ℝ} {E : Set ℝ} (W : EmbeddingIntrinsicProfile.{u} a c w0 T E) :
    NormalIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old | old | old | raw
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr (Or.inl old))
    · exact Or.inr (Or.inr (Or.inr (Or.inl old)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr old)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (embeddingTransfer_to_normal coordinates raw))))
/-- **Math.** Existing normal profiles remain admissible with no added assumptions. -/
def NormalIntrinsicProfile.toEmbedding {a c w0 T : ℝ} {E : Set ℝ}
    (W : NormalIntrinsicProfile.{u} a c w0 T E) : EmbeddingIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with old | old | old | old | old
    · exact Or.inl old
    · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr (Or.inl old))
    · exact Or.inr (Or.inr (Or.inr (Or.inl old)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl old))))
/-- **Math.** Open research: actual controlled flow, good sweepouts and relative approximants. -/
def EmbeddingGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (EmbeddingIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem normal_producer_of_embedding (coordinates : EmbeddedNormalCoordinatesStatement.{u})
    (produce : EmbeddingGeometryProducerStatement.{u}) : NormalGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toNormal coordinates⟩
/-- **Math.** Four independent leaves construct normal coordinates and feed the same public root. -/
theorem public_of_embedded_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (inverse : TubularChartInverseStatement.{u})
    (frames : EmbeddedNormalFrameStatement.{u}) (transport : NormalFrameTransportStatement.{u})
    (parametrize : NormalBundleParametrizationStatement.{u})
    (regularity : NormalParametrizationRegularityStatement.{u})
    (geometry : EmbeddingGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_twenty_nine triangulate atlas inverse (normal_producer_of_embedding
    (embedded_normal_coordinates_of_leaves frames transport parametrize regularity) geometry)
#print axioms EmbeddingIntrinsicProfile.toNormal
#print axioms NormalIntrinsicProfile.toEmbedding
#print axioms normal_producer_of_embedding
#print axioms public_of_embedded_frontier
end PoincareConjecture.ProofContract.Refinement20260927
