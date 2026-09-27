import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationConstruction
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Actual Euclidean approximants, not already-manifold-valued approximants. -/
def AmbientClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : AmbientApproximationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.reference (x,p)) ≤ (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem ambientTransfer_to_embedding (frames : EmbeddedNormalFrameStatement.{u})
    (control : CompactRetractionControlStatement.{u}) (chain : SphereCompositionEstimateStatement)
    (correct : AmbientEndpointCorrectionStatement) (confine : AmbientSweepoutConfinementStatement)
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : AmbientClassTransfer source target t) :
    EmbeddingClassTransfer source target t := by
  intro i
  obtain ⟨r,he⟩ := h i
  obtain ⟨out,hout⟩ := r.toEmbedding frames control chain correct confine
  refine ⟨out,?_⟩
  intro x
  rw [hout]
  exact he x
/-- **Math.** The new route is added without invalidating any older transfer entrance. -/
structure AmbientIntrinsicProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → IntrinsicSpectrumData.{u}
  after : ℝ → IntrinsicSpectrumData.{u}
  initial : ((after 0).spectrum checked_sphere_energy_continuity).width 0 ≤ w0
  transfer : ∀ t ∈ events,
    ApproximateSweepoutTransfer ((before t).spectrum checked_sphere_energy_continuity)
      ((after t).spectrum checked_sphere_energy_continuity) t ∨
        RegularizedClassTransfer (before t) (after t) t ∨ RetractionClassTransfer (before t) (after t) t ∨
          TubularClassTransfer (before t) (after t) t ∨ NormalClassTransfer (before t) (after t) t ∨ EmbeddingClassTransfer (before t) (after t) t ∨ AmbientClassTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ d : IntrinsicSpectrumData.{u}, MorganTianLib.IsSmoothMetricFamilyOn d.metric (Icc s t) ∧
      (d.spectrum checked_sphere_energy_continuity).width s =
        ((after s).spectrum checked_sphere_energy_continuity).width s ∧
      (d.spectrum checked_sphere_energy_continuity).width t =
        ((before t).spectrum checked_sphere_energy_continuity).width t ∧
      ∀ r ∈ Ico s t, Nonempty
        (GoodSweepoutAt (d.spectrum checked_sphere_energy_continuity) r a (3/(4*(r+c))))
def AmbientIntrinsicProfile.toEmbedding (frames : EmbeddedNormalFrameStatement.{u})
    (control : CompactRetractionControlStatement.{u}) (chain : SphereCompositionEstimateStatement)
    (correct : AmbientEndpointCorrectionStatement) (confine : AmbientSweepoutConfinementStatement)
    {a c w0 T : ℝ} {E : Set ℝ} (W : AmbientIntrinsicProfile.{u} a c w0 T E) :
    EmbeddingIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (ambientTransfer_to_embedding frames control chain correct confine h)))))
/-- **Math.** Old profiles need no new hypotheses or raw approximants. -/
def EmbeddingIntrinsicProfile.toAmbient {a c w0 T : ℝ} {E : Set ℝ}
    (W : EmbeddingIntrinsicProfile.{u} a c w0 T E) : AmbientIntrinsicProfile.{u} a c w0 T E where
  before := W.before
  after := W.after
  initial := W.initial
  intervals := W.intervals
  transfer := by
    intro t ht
    rcases W.transfer t ht with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
/-- **Math.** Controlled flow, sweepout estimates and actual ambient C1 approximants remain research. -/
def AmbientGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ, 0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (AmbientIntrinsicProfile.{u} a c w0 H.horizon H.events))
theorem embedding_producer_of_ambient (frames : EmbeddedNormalFrameStatement.{u})
    (control : CompactRetractionControlStatement.{u}) (chain : SphereCompositionEstimateStatement)
    (correct : AmbientEndpointCorrectionStatement) (confine : AmbientSweepoutConfinementStatement)
    (produce : AmbientGeometryProducerStatement.{u}) : EmbeddingGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hs
  obtain ⟨W⟩ := profile hs
  exact ⟨W.toEmbedding frames control chain correct confine⟩
/-- **Math.** Exact public V1 conclusion from the existing frame leaf and four new independent leaves. -/
theorem public_of_ambient_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (frames : EmbeddedNormalFrameStatement.{u})
    (control : CompactRetractionControlStatement.{u}) (chain : SphereCompositionEstimateStatement)
    (correct : AmbientEndpointCorrectionStatement) (confine : AmbientSweepoutConfinementStatement)
    (geometry : AmbientGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_thirty_three triangulate atlas frames
    (embedding_producer_of_ambient frames control chain correct confine geometry)
#print axioms ambientTransfer_to_embedding
#print axioms AmbientIntrinsicProfile.toEmbedding
#print axioms EmbeddingIntrinsicProfile.toAmbient
#print axioms embedding_producer_of_ambient
#print axioms public_of_ambient_frontier
end PoincareConjecture.ProofContract.Refinement20260927
