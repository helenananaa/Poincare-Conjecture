import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalFrames
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- **Math.** Construct the actual normal total-space coordinates from four independent proofs. -/
theorem embedded_normal_coordinates_of_leaves (frames : EmbeddedNormalFrameStatement.{u})
    (transport : NormalFrameTransportStatement.{u})
    (parametrize : NormalBundleParametrizationStatement.{u})
    (regularity : NormalParametrizationRegularityStatement.{u}) :
    EmbeddedNormalCoordinatesStatement.{u} := by
  intro N n e
  letI : MetricSpace N := TopologicalSpace.metrizableSpaceMetric N
  let F (p : N) : EmbeddedNormalFrameAt e p := Classical.choice (frames N n e p)
  let h (p : N) : NormalFrameTransportLaws (F p) := transport N n e p (F p)
  let r (p : N) : NormalBundleParametrization (F p) :=
    Classical.choice (parametrize N n e p (F p) (h p))
  let zero : C(N,EmbeddedNormalTotal e) :=
    ⟨embeddedNormalZero e, (continuous_id.prodMk continuous_const).subtype_mk _⟩
  let project : C(EmbeddedNormalTotal e,N) :=
    ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩
  let endpoint : C(EmbeddedNormalTotal e,ApproxAmbient n) :=
    ⟨fun z => e.map z.val.1 + z.val.2,
      (e.map.continuous.comp (continuous_fst.comp continuous_subtype_val)).add
        (continuous_snd.comp continuous_subtype_val)⟩
  refine ⟨{ total := EmbeddedNormalTotal e
            metric := inferInstance
            zero := zero
            project := project
            endpoint := endpoint
            project_zero := fun p => rfl
            endpoint_zero := ?_
            linear := fun p => (F p).linear
            linear_injective := fun p => (F p).linear_injective
            base := fun p => (F p).baseChart p
            chart := fun p => (r p).chart
            zero_source := ?_
            zero_chart := fun p => (r p).zero_chart
            f := fun p => e.map ∘ (F p).baseChart.symm
            P := fun p => normalFrameForward (F p) ∘ (F p).baseChart.symm
            f_deriv := fun p => (F p).embedding_deriv
            P_deriv := ?_
            P_normal := ?_
            endpoint_formula := ?_
            smooth_expression := ?_
            smooth_projection := ?_ }⟩
  · intro p
    exact add_zero (e.map p)
  · intro p
    rw [(r p).source_eq]
    exact (F p).point_source
  · intro p
    exact ((h p).smooth_forward.contDiffAt
      ((F p).baseChart.open_target.mem_nhds
        ((F p).baseChart.map_source (F p).point_source))).differentiableAt (by simp)
  · intro p v
    change normalFrameForward (F p) ((F p).baseChart.symm ((F p).baseChart p)) v = v
    rw [(F p).baseChart.left_inv (F p).point_source]
    exact (h p).center_identity v
  · intro p z hz
    change e.map ((r p).chart.symm z).val.1 + ((r p).chart.symm z).val.2 =
      e.map ((F p).baseChart.symm z.1) + normalFrameForward (F p) ((F p).baseChart.symm z.1) z.2
    rw [(r p).inverse_base z hz, (r p).inverse_vector z hz]
  · intro p
    exact (regularity N n e p (F p) (h p) (r p)).1
  · intro p
    exact (regularity N n e p (F p) (h p) (r p)).2
/-- **Math.** Genuine local retraction existence follows, not just conditional data conversion. -/
theorem embedded_retraction_of_frame_leaves (frames : EmbeddedNormalFrameStatement.{u})
    (transport : NormalFrameTransportStatement.{u})
    (parametrize : NormalBundleParametrizationStatement.{u})
    (regularity : NormalParametrizationRegularityStatement.{u})
    (inverse : TubularChartInverseStatement.{u})
    (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map := by
  obtain ⟨T⟩ := embedded_normal_coordinates_of_leaves frames transport parametrize regularity N n e
  exact T.toRetraction checked_normal_linear_equiv checked_normal_endpoint_jet inverse
#print axioms embedded_normal_coordinates_of_leaves
#print axioms embedded_retraction_of_frame_leaves
end PoincareConjecture.ProofContract.Refinement20260927
